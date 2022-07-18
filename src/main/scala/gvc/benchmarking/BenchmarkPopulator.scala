package gvc.benchmarking

import gvc.benchmarking.DAO.DBConnection
import gvc.transformer.IR.Program
import gvc.Main

import java.nio.file.{Files, Path}
import scala.collection.mutable

object BenchmarkPopulator {

  case class ProgramInformation(src: String,
                                ir: Program,
                                labels: LabelOutput,
                                fileName: String)

  case class StoredProgramRepresentation(info: ProgramInformation,
                                         componentMapping: Map[ASTLabel, Long])

  def populate(populatorConfig: PopulatorConfig,
               libraryDirs: List[String]): Unit = {
    val connection = DAO.connect(populatorConfig.db)

    val programIDMapping =
      syncPrograms(populatorConfig.sources, libraryDirs, connection)

    programIDMapping.foreach(programRep => {
      populateProgram(programRep._1, programRep._2, populatorConfig, connection)
    })
  }

  def populateProgram(programID: Long,
                      programRep: StoredProgramRepresentation,
                      config: PopulatorConfig,
                      xa: DBConnection): Unit = {
    val theoreticalMax =
      LabelTools.theoreticalMaxPaths(programRep.info.labels.labels.size)
    if (config.pathQuantity > theoreticalMax) {
      Output.info(s"""The requested number of paths to generate is greater
           | than the theoretical max for ${programRep.info.fileName} ( ${config.pathQuantity} > $theoreticalMax).
            """.stripMargin)
    }

    val sampler = new Sampler(programRep.info.labels)
    Output.info(s"Generating paths for ${programRep.info.fileName}")

    val bottomPermutationHash =
      new LabelPermutation(programRep.info.labels).id.toString(16)
    val bottomPerm =
      DAO.addOrResolvePermutation(programID, bottomPermutationHash, xa)

    var currentPath = 1
    val maximum = BigInt
      .int2bigInt(config.pathQuantity)
      .min(theoreticalMax)
    while (DAO.getNumberOfPaths(programID, xa) < maximum) {
      print(
        Output.formatInfo(
          s"Generating path $currentPath out of ${maximum.toString}"))
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
          val currentID = currentPermutation.id.toString(16)
          val storedPermutationID =
            DAO.addOrResolvePermutation(programID, currentID, xa)
          pathQuery.addStep(storedPermutationID,
                            programRep.componentMapping(ordering(labelIndex)))
        }
        pathQuery.exec(xa)
      }
      print("\r")
      currentPath += 1
    }
    Output.success(
      s"Completed generating paths for ${programRep.info.fileName}")
  }

  def syncPrograms(programList: List[Path],
                   libraries: List[String],
                   xa: DBConnection): Map[Long, StoredProgramRepresentation] = {

    val programIDMapping = mutable.Map[Long, StoredProgramRepresentation]()

    programList.foreach(src => {
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
        print(
          Output.formatInfo(
            s"Resolving label ${i + 1} of ${labelOutput.labels.size}"))
        val l = labelOutput.labels(i)
        val insertedComponentID =
          DAO.addOrResolveComponent(insertedProgramID, l, xa)
        componentMapping += (l -> insertedComponentID)
        print("\r")
      })
      programIDMapping += (insertedProgramID -> StoredProgramRepresentation(
        programInfo,
        componentMapping.toMap))
      Output.success(s"Completed syncing ${src.getFileName}")
    })
    programIDMapping.toMap
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
