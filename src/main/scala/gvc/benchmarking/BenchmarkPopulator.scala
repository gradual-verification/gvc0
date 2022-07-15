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
                                         componentMapping: Map[Long, ASTLabel])

  private val BASELINE_QUANTITY = 1024

  def populate(populatorConfig: PopulatorConfig): Unit = {
    val connection = DAO.connect(populatorConfig.db)

    val programIDMapping = syncPrograms(populatorConfig.sources, connection)

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
      Output.info(
        s"""The requested number of paths to generate is greater
           | than the theoretical max for ${programRep.info.fileName} ( ${config.pathQuantity} > $theoreticalMax).
            """.stripMargin)
    }
    while (DAO.getNumberOfPaths(programID, xa) < Math.min(config.pathQuantity, theoreticalMax)) {


    }
  }

  def syncPrograms(programList: List[Path],
                   xa: DBConnection): Map[Long, StoredProgramRepresentation] = {

    val programIDMapping = mutable.Map[Long, StoredProgramRepresentation]()

    programList.foreach(src => {
      val sourceText = Files.readString(src)
      val sourceIR = Main.generateIR(sourceText, List())
      val labelOutput = new LabelVisitor().visit(sourceIR)
      val fileName = src.getFileName.toString
      val programInfo =
        ProgramInformation(sourceText, sourceIR, labelOutput, fileName)

      val insertedProgram = DAO.addOrResolveProgram(src,
        md5sum(sourceText),
        labelOutput.labels.size,
        xa)

      val componentMapping = mutable.Map[Long, ASTLabel]()
      labelOutput.labels.foreach(l => {
        val insertedComponent =
          DAO.addOrResolveComponent(insertedProgram, l, xa)
        componentMapping += (insertedComponent.id -> l)
      })

      programIDMapping += (insertedProgram.id -> StoredProgramRepresentation(
        programInfo,
        componentMapping.toMap))
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
