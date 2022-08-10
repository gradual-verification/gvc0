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
    val DateFormat = "+dd:MM:yyyy+HH:mm:ss+"
    val ErrorCSV: String = csv("errors")
    val DefaultMassOutputDir: String = "export-mass" + new SimpleDateFormat(
      Names.DateFormat).format(Calendar.getInstance().getTime)
    val DefaultBenchOutputDir: String = "export-bench" + new SimpleDateFormat(
      Names.DateFormat).format(Calendar.getInstance().getTime)
    val BenchmarkPerformanceCSV: String = csv("benchmark_perf")
    val DynamicPerformanceCSV: String = csv("dynamic_perf")
    val StaticPerformanceCSV: String = csv("static_perf")
    val PathIndexCSV: String = csv("path_index")
    val ProgramIndexCSV: String = csv("program_index")
    val ErrorCSVColumnNames =
      "version_name,hardware_name,permutation_id,error_type,error_desc,error_date"
    val DynamicPerformanceCSVColumnNames =
      "program_id,permutation_id,measurement_type,stress,iter,ninetyFifth,fifth,median,mean,stdev,min,max"
    val StaticPerformanceCSVColumnNames =
      "permutation_id,conj_elim,conj_total"
    val PathIndexCSVColumnNames =
      "program_id,permutation_id,path_id,level_id"
    val ProgramIndexCSVColumnNames =
      "program_name,program_id"
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
      case None        => error(s"Unable to find hardware '${config.hardware}'.")
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

    val pathIDsToPull =
      DAO.Exporter.getPathIDList(id.versionID, id.hardwareID, stressTable, conn)

    val grandList = (config.quantity match {
      case Some(value) =>
        pathIDsToPull.flatMap(p => {
          if (p._2.length < value) {
            DAO.resolveProgramName(p._1, conn) match {
              case Some(name) =>
                error(
                  s"There were only ${p._2.size} paths of $name matching the criteria, but $value were requested.")
              case None =>
                error(
                  s"There were only ${p._2.size} paths of PID=${p._1} matching the criteria, but $value were requested.")
            }
          } else {
            p._2.slice(0, value)
          }
        })
      case None => pathIDsToPull.flatMap(p => p._2)
    }).toList
    Output.info("Generating path index...")
    val pathIndex = DAO.Exporter.generatePathIndex(grandList, conn)
    Output.info("Generating program index...")
    val programIndex =
      DAO.Exporter.generateProgramIndexFromPaths(grandList, conn)

    Output.info("Collecting dynamic performance data...")
    val dynamicData =
      DAO.Exporter.generateDynamicPerformanceData(stressTable, grandList, conn)
    Output.info("Collecting static performance data...")
    val staticData =
      DAO.Exporter.generateStaticPerformanceData(grandList, conn)

    val outDir = Paths.get(
      config.outputDir.getOrElse(
        Names.DefaultMassOutputDir + List(config.hardware, config.version)
          .mkString("+")))

    Output.success(s"All data collected, writing to ${outDir.toString}")

    Files.createDirectories(outDir)

    val pathIndexPath = outDir.resolve(Names.PathIndexCSV)
    Files.writeString(
      pathIndexPath,
      List(Names.PathIndexCSVColumnNames, pathIndex).mkString("\n"))

    val programIndexPath = outDir.resolve(Names.ProgramIndexCSV)
    Files.writeString(
      programIndexPath,
      List(Names.ProgramIndexCSVColumnNames, programIndex).mkString("\n"))

    val dynamicPerformancePath = outDir.resolve(Names.DynamicPerformanceCSV)
    Files.writeString(
      dynamicPerformancePath,
      List(Names.DynamicPerformanceCSVColumnNames, dynamicData).mkString("\n"))

    val staticPerformancePath = outDir.resolve(Names.StaticPerformanceCSV)
    Files.writeString(
      staticPerformancePath,
      List(Names.StaticPerformanceCSVColumnNames, staticData).mkString("\n"))
  }

  private def exportBenchmark(config: ExportConfig,
                              id: AssertedPartialIdentity,
                              conn: DBConnection): Unit = {
    val stressTable = new StressTable(config.workload)
    val benchmarkIDsToPull = DAO.Exporter.getBenchmarkIDList(id.versionID,
                                                             id.hardwareID,
                                                             stressTable,
                                                             conn)
    if (benchmarkIDsToPull.isEmpty) {
      error("No completed benchmarks match the given criteria.")
    } else {
      val outDir = Paths.get(
        config.outputDir.getOrElse(
          Names.DefaultBenchOutputDir + List(config.hardware, config.version)
            .mkString("+")))
      Output.success(
        s"Found ${benchmarkIDsToPull.size} benchmark(s) that match the given criteria, writing to ${outDir.toString}")
      Files.createDirectories(outDir)

      val programIndex = DAO.Exporter.generateProgramIndex(conn)
      val programIndexPath = outDir.resolve(Names.ProgramIndexCSV)
      Files.writeString(
        programIndexPath,
        List(Names.ProgramIndexCSVColumnNames, programIndex).mkString("\n"))

      benchmarkIDsToPull.foreach(entry => {
        Output.info(s"Pulling data for benchmark '${entry.name}'...")
        val performance =
          DAO.Exporter.getBenchmarkPerformanceData(stressTable, entry.id, conn)
        val benchmarkPerformancePath = outDir.resolve(csv(entry.name + "_perf"))
        Files.writeString(benchmarkPerformancePath,
                          List(Names.DynamicPerformanceCSVColumnNames,
                               performance).mkString("\n"))
      })
    }
  }

  private def exportErrors(config: ExportConfig,
                           id: AssertedPartialIdentity,
                           conn: DBConnection): Unit = {
    val errorContents = DAO.getErrorList(id.versionID, id.hardwareID, conn)
    val outputCSV = Paths.get(
      config.outputDir.getOrElse(Names.DefaultMassOutputDir),
      Names.ErrorCSV)
    Files.writeString(
      outputCSV,
      List(Names.ErrorCSVColumnNames, errorContents).mkString("\n"))
  }
}
