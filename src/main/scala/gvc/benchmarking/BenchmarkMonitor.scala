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
        Output.info(s"    Program: ${r2._1}")
        r2._2.foreach(r3 => {
          Output.info(s"        Mode: ${r3._1}")
          r3._2.foreach(r4 => {
            Output.info(
              s"            Status: ${r4.totalCompleted}/${r4.total} - ${Math
                .round(r4.totalCompleted.toDouble / r4.total * 100)
                .toInt}%")
          })
        })
      })
    })
  }

  def sortResults(results: List[DAO.CompletionMetadata]): Map[
    String,
    Map[String, Map[DynamicMeasurementMode, List[CompletionMetadata]]]] = {
    results
      .groupBy(_.versionName)
      .map(pair => {
        pair._1 -> pair._2
          .groupBy(_.srcFilename)
          .map(pair2 => {
            pair2._1 -> pair2._2.groupBy(_.measurementMode)
          })
      })
  }
}
