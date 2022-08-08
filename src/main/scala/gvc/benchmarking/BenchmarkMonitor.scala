package gvc.benchmarking

import gvc.benchmarking.Benchmark.Extensions.csv
import gvc.benchmarking.DAO.DBConnection
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode

object BenchmarkMonitor {
  def monitor(config: MonitorConfig): Unit = {
    val conn = DAO.connect(config.db)
    logStatistics(config, conn)
  }
  private object Names {
    val errorListing: DynamicMeasurementMode = csv("errors")
    val dynamicPerformanceListing: DynamicMeasurementMode = csv(
      "dynamic_performance")
    val staticPerformanceListing: DynamicMeasurementMode = csv(
      "static_performance")
    val errorContentsColumns =
      "permutation_id,version_name,src_filename,mode,error_type,error_desc"
  }

  private def logStatistics(config: MonitorConfig, conn: DBConnection): Unit = {
    val metadata = DAO.getCompletionMetadata(conn)
    printResults(metadata)
  }

  private def printResults(metadata: List[DAO.CompletionMetadata]): Unit = {
    val structured = metadata
      .groupBy(_.versionName)
      .map(g => {
        g._1 -> g._2
          .groupBy(_.hardwareName)
          .map(h => {
            h._1 -> h._2
          })
      })
    structured.keySet.foreach(k => {
      println(k)
      structured(k).foreach(m => {
        println(
          "\t\t" + m._1 + s" — %${Math.round(m._2.head.percentCompleted * 10) / 10}")
        println("\t\t\t Errors:")
        m._2.head.errorMapping.foreach(em => {
          println(s"\t\t\t${em._1} — ${em._2}")
        })
      })
    })
  }
}
