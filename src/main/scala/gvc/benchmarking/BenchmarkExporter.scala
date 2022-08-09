package gvc.benchmarking

import gvc.Config.error
import gvc.benchmarking.Benchmark.Extensions._
import gvc.benchmarking.BenchmarkExecutor.StressTable
import gvc.benchmarking.DAO.DBConnection

import java.nio.file.{Files, Paths}
import java.text.SimpleDateFormat
import java.util.Calendar

object BenchmarkExporter {

  private case class AssertedPartialIdentity(versionID: Long, hardwareID: Long)

  private object Names {
    val DateFormat = "+dd-MMM-yyyy+HH:mm:ss"
    val ErrorCSV: String = csv("errors")
    val DefaultOutputDir: String = "export" + new SimpleDateFormat(
      Names.DateFormat).format(Calendar.getInstance().getTime)
    val ErrorCSVColumnNames =
      "version_name,hardware_name,permutation_id,error_type,error_desc,error_date"
    val DynamicPathCSVColumnNames =
      "version_name,hardware_name,permutation_id,error_type,error_desc,error_date"
    val StaticPathCSVColumnNames =
      "version_name,hardware_name,permutation_id,error_type,error_desc,error_date"
  }

  private def resolvePartialIdentity(
      config: ExportConfig,
      conn: DBConnection): AssertedPartialIdentity = {
    val versionID = DAO.resolveVersion(config.version, conn) match {
      case Some(value) => value
      case None        => error(s"Unable to find version '${config.version}'.")
    }
    val hardwareID = DAO.resolveHardware(config.hardware, conn) match {
      case Some(value) => value
      case None        => error(s"Unable to find version '${config.version}'.")
    }
    AssertedPartialIdentity(versionID, hardwareID)
  }

  def export(config: ExportConfig): Unit = {
    val conn = DAO.connect(config.benchmarkDBCredentials)
    val id = resolvePartialIdentity(config, conn)
    if (config.modifiers.onlyErrors) {
      exportErrors(config, id, conn)
    } else {
      if (config.modifiers.onlyBenchmark) {
        exportBenchmark(config, id, conn)
      } else {
        exportPaths(config, id, conn)
      }
    }
  }

  private def exportPaths(config: ExportConfig,
                          id: AssertedPartialIdentity,
                          conn: DBConnection): Unit = {
    val stressTable = new StressTable(config.workload)

  }

  private def exportBenchmark(config: ExportConfig,
                              identity: AssertedPartialIdentity,
                              conn: DBConnection): Unit = {
    val stressTable = new StressTable(config.workload)
    val quantityToQuery = config.quantity match {
      case Some(value) => value
      case None        => error("Must specify a <quantity> of paths to export.")
    }
  }

  private def exportErrors(config: ExportConfig,
                           id: AssertedPartialIdentity,
                           conn: DBConnection): Unit = {
    val errorContents = DAO.getErrorList(id.versionID, id.hardwareID, conn)
    val outputCSV = Paths.get(
      config.outputDir.getOrElse(Names.DefaultOutputDir),
      Names.ErrorCSV)
    Files.writeString(
      outputCSV,
      List(Names.ErrorCSVColumnNames, errorContents).mkString("\n"))
  }
}
