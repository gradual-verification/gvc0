package gvc.benchmarking

import gvc.Config.error
import gvc.benchmarking.DAO.{DBConnection, PathQueryCollection}
import gvc.transformer.IR.Program
import gvc.Main
import gvc.benchmarking.Benchmark.BenchmarkException

import scala.concurrent._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.{Failure, Success, Try}
import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.concurrent.Future
import scala.concurrent.duration.Duration

object BenchmarkPopulator {

  case class ProgramInformation(src: String,
                                ir: Program,
                                labels: LabelOutput,
                                fileName: String)

  case class StoredProgramRepresentation(info: ProgramInformation,
                                         componentMapping: Map[ASTLabel, Long])

  def futureToFutureTry[T](future: Future[T]): Future[Try[T]] =
    future map (Success(_)) recover { case x => Failure(x) }

  def allOf[T](futures: Seq[Future[T]]): Future[Seq[Try[T]]] =
    Future.sequence(futures map futureToFutureTry)

  def populate(populatorConfig: PopulatorConfig,
               libraryDirs: List[String]): Unit = {
    val connection = DAO.connect(populatorConfig.db)
    populatePrograms(populatorConfig.sources,
                     libraryDirs,
                     populatorConfig,
                     connection)
  }

  def sync(sources: List[Path],
           libraryDirs: List[String],
           connection: DBConnection): Map[Long, ProgramInformation] = {
    val synchronized = allOf(
      sources.map(src => {
        Future(syncProgram(src, libraryDirs, connection))
      })
    )
    val mapping = mutable.Map[Long, ProgramInformation]()
    Await
      .result(synchronized, Duration.Inf)
      .foreach {
        case Failure(f) => throw new BenchmarkException(f.getMessage)
        case Success(valueOption) =>
          valueOption match {
            case Some(value) => mapping += value
            case None        =>
          }
      }
    if (mapping.isEmpty) {
      error("Failed to resolve any programs.")
    } else {
      mapping.toMap
    }
  }

  def populatePrograms(
      sources: List[Path],
      libraryDirs: List[String],
      populatorConfig: PopulatorConfig,
      connection: DBConnection): Map[Long, StoredProgramRepresentation] = {

    val stressTable = new StressTable(populatorConfig.workload)

    val synchronized = allOf(
      sources
        .map(src => {
          Future(
            populateProgram(src,
                            libraryDirs,
                            populatorConfig,
                            stressTable,
                            connection))
        }))

    val mapping = mutable.Map[Long, StoredProgramRepresentation]()
    Await
      .result(synchronized, Duration.Inf)
      .foreach {
        case Failure(f) => throw new BenchmarkException(f.getMessage)
        case Success(value) =>
          Output.info(s"Storing paths for ${value.rep.info.fileName}")
          value.pathQueries.foreach(q => q.exec(connection))
          mapping += (value.id -> value.rep)
      }
    mapping.toMap
  }

  private def syncProgram(
      src: Path,
      libraries: List[String],
      conn: DBConnection): Option[(Long, ProgramInformation)] = {

    Output.info(s"Syncing definitions for ${src.getFileName}")

    val sourceText = Files.readString(src)
    val sourceIR = Main.generateIR(sourceText, libraries)
    val labelOutput = new LabelVisitor().visit(sourceIR)
    val fileName = src.getFileName.toString
    val programInfo =
      ProgramInformation(sourceText, sourceIR, labelOutput, fileName)

    val insertedProgramID =
      DAO.resolveProgram(md5sum(sourceText), labelOutput.labels.size, conn)

    insertedProgramID match {
      case Some(value) =>
        if (labelOutput.labels.indices.exists(i => {
              val l = labelOutput.labels(i)
              DAO.resolveComponent(value, l, conn).isEmpty
            })) None
        else {
          Some(value -> programInfo)
        }
      case None =>
        Output.error(s"Program $fileName isn't present in the database.")
        None
    }
  }

  private def populatePaths(programID: Long,
                            programRep: StoredProgramRepresentation,
                            populatorConfig: PopulatorConfig,
                            stressList: List[Int],
                            conn: DBConnection): List[PathQueryCollection] = {

    val theoreticalMax =
      LabelTools.theoreticalMaxPaths(programRep.info.labels.labels.size)
    val sampler = new Sampler(programRep.info.labels)
    Output.info(s"Generating paths for ${programRep.info.fileName}")
    val bottomPermutationHash =
      new LabelPermutation(programRep.info.labels).idArray

    val checksum = md5sum(bottomPermutationHash.toString)
    val bottomPerm =
      DAO.addOrResolvePermutation(programID,
                                  checksum,
                                  bottomPermutationHash,
                                  conn)
    Output.success(
      s"Resolved bottom permutation for program '${programRep.info.fileName}'")
    val queryCollections = mutable.ListBuffer[PathQueryCollection]()

    val alreadyCreatedPermutations = mutable.Map[String, Long]()
    val baselineMaximum =
      theoreticalMax
        .min(conn.gConfig.maxPaths)
    val configuredMaximum: BigInt = populatorConfig.pathQuantity match {
      case Some(value) => value
      case None        => baselineMaximum
    }
    val difference = configuredMaximum - DAO.getNumberOfPaths(programID, conn)
    for (i <- 0 until difference.intValue()) {
      val ordering = sampler.sample(SamplingHeuristic.Random)
      val pathHash =
        LabelTools
          .hashPath(programRep.info.labels.labels, ordering)
      if (!DAO.containsPath(programID, pathHash, conn)) {
        val pathQuery =
          new DAO.PathQueryCollection(pathHash, programID, bottomPerm)
        val currentPermutation =
          new LabelPermutation(programRep.info.labels)

        for (labelIndex <- ordering.indices) {
          currentPermutation.addLabel(ordering(labelIndex))
          val currentID = currentPermutation.idArray
          val checksum = md5sum(currentID.toString)
          val storedPermutationID =
            if (alreadyCreatedPermutations.contains(checksum)) {
              alreadyCreatedPermutations(checksum)
            } else {
              val id = DAO.addOrResolvePermutation(programID,
                                                   checksum,
                                                   currentID,
                                                   conn)
              alreadyCreatedPermutations += (checksum -> id)
              id
            }
          pathQuery.addStep(storedPermutationID,
                            programRep.componentMapping(ordering(labelIndex)))
        }
        queryCollections += pathQuery
        Output.success(s"Assembled path query ${i + 1}/${difference
          .intValue()} for program '${programRep.info.fileName}'")
      }
    }
    Output.success(
      s"Completed generating paths for ${programRep.info.fileName}")
    queryCollections.toList
  }

  case class PopulatedProgram(id: Long,
                              rep: StoredProgramRepresentation,
                              pathQueries: List[PathQueryCollection])

  private def populateProgram(src: Path,
                              libraries: List[String],
                              populatorConfig: PopulatorConfig,
                              stressTable: StressTable,
                              xa: DBConnection): PopulatedProgram = {
    Output.info(s"Syncing definitions for ${src.getFileName}")
    val sourceText = Files.readString(src)
    val sourceIR = Main.generateIR(sourceText, libraries)
    val labelOutput = new LabelVisitor().visit(sourceIR)
    val fileName = src.getFileName.toString
    val programInfo =
      ProgramInformation(sourceText, sourceIR, labelOutput, fileName)
    val insertedProgramID = DAO.addOrResolveProgram(src,
                                                    md5sum(sourceText),
                                                    labelOutput.labels.size,
                                                    xa)
    DAO.addProgramWorkloadMappings(insertedProgramID, stressTable.get(src), xa)

    val componentMapping = mutable.Map[ASTLabel, Long]()
    labelOutput.labels.indices.foreach(i => {
      val l = labelOutput.labels(i)
      val insertedComponentID =
        DAO.addOrResolveComponent(insertedProgramID, l, xa)
      Output.success(s"Resolved component ${l.hash}")
      componentMapping += (l -> insertedComponentID)
    })
    Output.success(s"Completed syncing ${src.getFileName}")

    val programRep =
      StoredProgramRepresentation(programInfo, componentMapping.toMap)
    PopulatedProgram(insertedProgramID,
                     programRep,
                     populatePaths(insertedProgramID,
                                   programRep,
                                   populatorConfig,
                                   stressTable.get(src),
                                   xa))
  }

  //https://alvinalexander.com/source-code/scala-method-create-md5-hash-of-string/
  def md5sum(contents: String): String = {

    def prependWithZeros(pwd: String): String =
      "%1$32s".format(pwd).replace(' ', '0')

    import java.math.BigInteger
    import java.security.MessageDigest
    val md = MessageDigest.getInstance("MD5")
    val digest: Array[Byte] = md.digest(contents.getBytes)
    val bigInt = new BigInteger(1, digest)
    val hashedPassword = bigInt.toString(16).trim
    prependWithZeros(hashedPassword)
  }

  class StressTable(workload: BenchmarkWorkload) {
    private val defaultStressValues = workload.stress match {
      case Some(value) => BenchmarkExternalConfig.generateStressList(value)
      case None =>
        workload.programCases.find(p => p.isDefault) match {
          case Some(value) =>
            BenchmarkExternalConfig.generateStressList(value.workload)
          case None => error("Unable to resolve default stress configuration.")
        }
    }
    private val userConfiguredStressMappings = workload.programCases
      .flatMap(c => {
        val stressValues =
          BenchmarkExternalConfig.generateStressList(c.workload)
        for {
          i1: String <- c.matches
        } yield i1 -> stressValues
      })
      .toMap

    def get(src: Path): List[Int] = {
      val fileName = src.getFileName.toString
      val baseName = fileName.substring(0, fileName.lastIndexOf(".c0"))
      userConfiguredStressMappings.get(baseName) match {
        case Some(value) => value
        case None        => defaultStressValues
      }
    }
  }
}
