package gvc.benchmarking

import gvc.benchmarking.DAO.CompletionMetadata
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import java.util.Calendar

object BenchmarkMonitor {

  def monitor(config: MonitorConfig): Unit = {
    val conn = DAO.connect(config.db)
    val results = DAO.listPerformanceResults(conn)
    val sortedResults = sortResults(results)
    print("\u001b[2J")
    Output.info(s"Last Updated: ${Calendar.getInstance().getTime.toString}")
    sortedResults.foreach(r => {
      Output.info(s"Version: ${r._1}")
      r._2.foreach(r2 => {
        Output.info(s"    * Program: ${r2._1}")
        r2._2.foreach(r3 => {
          Output.info(s"          * Mode: ${r3._1}")
          r3._2.foreach(r4 => {
            Output.info(s"            * Filename: ${r4._1}")
            val categoryData = r4._2
            Output.info(
              s"              * Success: ${categoryData.totalCompleted}/${categoryData.total} - ${Math
                .round(categoryData.totalCompleted.toDouble / categoryData.total * 100)
                .toInt}%")
            if (categoryData.errorCountListing.nonEmpty) {
              Output.info(s"              * Errors")
              categoryData.errorCountListing.foreach(pair =>
                Output.info(s"                  * ${pair._1}: ${pair._2}"))
            }
          })
        })
      })
    })
  }

  case class CompletedCategory(srcFileName: String,
                               errorCountListing: Map[String, Long],
                               totalCompleted: Long,
                               total: Long)

  def sortResults(results: List[DAO.CompletionMetadata])
    : Map[String,
          Map[String,
              Map[DynamicMeasurementMode, Map[String, CompletedCategory]]]] = {
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
                    pair4._1 -> createCategory(pair4._2)
                  })
              })
          })
      })

  }

  def createCategory(
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
