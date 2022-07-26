package gvc.benchmarking

import gvc.benchmarking.DAO.{DBConnection, GlobalConfiguration}
import gvc.transformer.IR.Program
import gvc.Main
import gvc.benchmarking.BenchmarkSequential.BenchmarkException

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
    val globalConfig = DAO.resolveGlobalConfiguration(connection)
    syncPrograms(populatorConfig.sources, libraryDirs, globalConfig, connection)
  }

  def syncPrograms(
      sources: List[Path],
      libraryDirs: List[String],
      globalConfig: GlobalConfiguration,
      connection: DBConnection): Map[Long, StoredProgramRepresentation] = {

    sources
      .map(src => {
        syncProgram(src, libraryDirs, globalConfig, connection)
      })
      .toMap
    /*
    val mapping = mutable.Map[Long, StoredProgramRepresentation]()
    Await
      .result(synchronized, Duration.Inf)
      .foreach {
        case Failure(f) => throw new BenchmarkException(f.getMessage)
        case Success(value) => mapping += value
      }
    mapping.toMap*/
  }

  private def syncProgram(
      src: Path,
      libraries: List[String],
      globalConfiguration: GlobalConfiguration,
      xa: DBConnection): (Long, StoredProgramRepresentation) = {
    val storedRep =
      this.populateComponents(src, libraries, globalConfiguration, xa)
    populateProgram(storedRep._1, storedRep._2, globalConfiguration, xa)
    storedRep
  }

  private def populateProgram(programID: Long,
                              programRep: StoredProgramRepresentation,
                              globalConfig: GlobalConfiguration,
                              xa: DBConnection): Unit = {
    val theoreticalMax =
      LabelTools.theoreticalMaxPaths(programRep.info.labels.labels.size)

    val sampler = new Sampler(programRep.info.labels)
    Output.info(s"Generating paths for ${programRep.info.fileName}")
    val bottomPermutationHash =
      new LabelPermutation(programRep.info.labels).idArray
    val bottomPerm =
      DAO.addOrResolvePermutation(programID, bottomPermutationHash, xa)

    val maximum = theoreticalMax.min(globalConfig.maxPaths)
    while (DAO.getNumberOfPaths(programID, xa) < maximum) {
      val ordering = sampler.sample(SamplingHeuristic.Random)
      val pathHash =
        LabelTools
          .hashPath(programRep.info.labels.labels, ordering)
          .toString(16)
      if (!DAO.containsPath(programID, pathHash, xa)) {
        val pathQuery =
          new DAO.PathQueryCollection(pathHash, programID, bottomPerm)

        val currentPermutation =
          new LabelPermutation(programRep.info.labels)

        for (labelIndex <- ordering.indices) {
          currentPermutation.addLabel(ordering(labelIndex))
          val currentID = currentPermutation.idArray
          val storedPermutationID =
            DAO.addOrResolvePermutation(programID, currentID, xa)
          pathQuery.addStep(storedPermutationID,
                            programRep.componentMapping(ordering(labelIndex)))

          val recreated = new LabelPermutation(programRep.info.labels)
          currentPermutation.labels.foreach(recreated.addLabel)
          val selected = new SelectVisitor(programRep.info.ir).visit(recreated)

          val decoded = LabelTools.permutationIDToPermutation(
            programRep.info.labels,
            currentID)

          val selectDecoded =
            new SelectVisitor(programRep.info.ir).visit(decoded)
        }
        pathQuery.exec(xa)
      }
    }
    Output.success(
      s"Completed generating paths for ${programRep.info.fileName}")
  }

  private def populateComponents(
      src: Path,
      libraries: List[String],
      globalConfiguration: GlobalConfiguration,
      xa: DBConnection): (Long, StoredProgramRepresentation) = {
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
    val componentMapping = mutable.Map[ASTLabel, Long]()
    labelOutput.labels.indices.foreach(i => {
      val l = labelOutput.labels(i)
      val insertedComponentID =
        DAO.addOrResolveComponent(insertedProgramID, l, xa)
      componentMapping += (l -> insertedComponentID)
    })
    Output.success(s"Completed syncing ${src.getFileName}")

    val programRep =
      StoredProgramRepresentation(programInfo, componentMapping.toMap)
    populateProgram(insertedProgramID, programRep, globalConfiguration, xa)

    (insertedProgramID, programRep)
  }

  //https://alvinalexander.com/source-code/scala-method-create-md5-hash-of-string/
  private def md5sum(contents: String): String = {

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

}
