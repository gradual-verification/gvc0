package gvc.benchmarking

import gvc.benchmarking.Benchmark.Extensions.csv
import gvc.benchmarking.DAO.{CompletionMetadata, DBConnection}
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode

import java.nio.file.Files
import java.util.Calendar

object BenchmarkMonitor {

  def monitor(config: MonitorConfig): Unit = {
    val conn = DAO.connect(config.db, config)
    printContentsSummary(conn)
    logStatistics(config, conn)
  }

  private object Names {
    val errorListing: DynamicMeasurementMode = csv("errors")
    val dynamicPerformanceListing: DynamicMeasurementMode = csv(
      "dynamic_performance")
    val staticPerformanceListing: DynamicMeasurementMode = csv(
      "static_performance")
    val errorContentsColumns =
      "permutation_id,version_name,src_filename,mode,time_elapsed_seconds,error_type,error_desc"
  }

  private def printContentsSummary(conn: DBConnection): Unit = {
    val results = DAO.listPerformanceResults(conn)
    val sortedResults = sortResults(results)
    print("\u001b[2J")
    Output.info(s"Last Updated: ${Calendar.getInstance().getTime.toString}")
    sortedResults.foreach(r => {
      Output.info(s"Version: ${r._1}")
      r._2.foreach(r2 => {
        Output.info(s"    * Hardware: ${r2._1}")
        r2._2.foreach(r3 => {
          Output.info(s"          * Mode: ${r3._1}")
          r3._2.foreach(r4 => {
            Output.info(s"              * Filename: ${r4._1}")
            r4._2.foreach(r5 => {
              Output.info(s"                  * Stress: ${r5._1}")
              val categoryData = r5._2
              Output.info(s"                        * Success: ${categoryData.totalCompleted}/${categoryData.total} - ${Math
                .round(categoryData.totalCompleted.toDouble / categoryData.total * 100)
                .toInt}%")
              if (categoryData.errorCountListing.nonEmpty) {
                Output.info(s"                        * Errors")
                categoryData.errorCountListing.foreach(pair =>
                  Output.info(
                    s"                          * ${pair._1}: ${pair._2}"))
              }
            })
          })
        })
      })
    })
  }

  private def logStatistics(config: MonitorConfig, conn: DBConnection): Unit = {
    if (Files.notExists(config.outputDirectory)) {
      Files.createDirectories(config.outputDirectory)
    }

    val errors = config.outputDirectory.resolve(this.Names.errorListing)
    Files.writeString(errors, this.generateErrorCSV(conn))
  }

  private def generateErrorCSV(conn: DBConnection): String = {
    val errors = DAO.listErrors(conn)

    (List(Names.errorContentsColumns) ++
      errors
        .map(e => {
          List(e.pid,
               e.versionName,
               e.programName,
               e.measurementMode,
               e.timeSeconds,
               e.errorType,
               e.errorDesc).mkString(",")
        }))
      .mkString("\n")
  }

  private case class CompletedCategory(srcFileName: String,
                                       errorCountListing: Map[String, Long],
                                       totalCompleted: Long,
                                       total: Long)

  private def sortResults(results: List[DAO.CompletionMetadata])
    : Map[String,
          Map[String,
              Map[DynamicMeasurementMode,
                  Map[String, Map[Long, CompletedCategory]]]]] = {
    results
      .groupBy(_.versionName)
      .map(pair => {
        pair._1 -> pair._2
          .groupBy(_.hardwareName)
          .map(pair2 => {
            pair2._1 -> pair2._2
              .groupBy(_.measurementMode)
              .map(pair3 => {
                pair3._1 -> pair3._2
                  .groupBy(_.srcFilename)
                  .map(pair4 => {
                    pair4._1 -> pair4._2
                      .groupBy(_.stress)
                      .map(pair5 => pair5._1 -> createCategory(pair4._2))
                  })
              })
          })
      })
  }

  private def createCategory(
      completion: List[CompletionMetadata]): CompletedCategory = {

    val errorCountMapping = completion
      .filter(c => c.errorType.nonEmpty && c.errorCount.nonEmpty)
      .map(c => {
        c.errorType.get -> c.errorCount.get
      })
      .toMap
    val modifiedCompleted = completion.head.totalCompleted - errorCountMapping.values.sum
    CompletedCategory(completion.head.srcFilename,
                      errorCountMapping,
                      modifiedCompleted,
                      completion.head.total)
  }
}
