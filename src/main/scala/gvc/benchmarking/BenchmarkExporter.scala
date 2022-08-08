package gvc.benchmarking

object BenchmarkExporter {
  def export(config: ExportConfig): Unit = {
    val conn = DAO.connect(config.benchmarkDBCredentials)

  }
}
