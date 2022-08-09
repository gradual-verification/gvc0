package gvc.benchmarking

import gvc.benchmarking.Benchmark.Extensions.csv
import gvc.benchmarking.DAO.DBConnection
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.Output.{green, red}

object BenchmarkMonitor {
  def monitor(config: MonitorConfig): Unit = {
    val conn = DAO.connect(config.db)
    logStatistics(config, conn)
  }

  private def printContents(conn: DBConnection): Unit = {
    println("* Programs")
    val storedPrograms = DAO.getProgramList(conn)
    if (storedPrograms.nonEmpty) {
      storedPrograms.foreach(sp => {
        println(
          s"\t* ${sp.name} - ${sp.numPrograms} perms - ${sp.numPaths} paths - ${sp.numPerPath} perms/path")
      })
    } else {
      println("\tN/A")
    }

    println("* Benchmarks")
    val storedBenchmarks = DAO.getBenchmarkList(conn)
    if (storedBenchmarks.nonEmpty) {
      storedBenchmarks.foreach(b => {
        println(s"\t* ${b.name} - ${b.desc} - ${b.numPrograms} programs")
      })
    } else {
      println("\tN/A")
    }
  }

  private def logStatistics(config: MonitorConfig, conn: DBConnection): Unit = {

    Output.title("Database Contents")
    printContents(conn)

    Output.title("Incomplete Mass Benchmarks")
    printIncomplete(conn)

    Output.title("Completed Mass Benchmarks")
    printCompletedPaths(conn)

    Output.title("Completed Preconfigured Benchmarks")
    printCompletedBenchmarks(conn)

  }

  private def printCompletedPaths(conn: DBConnection): Unit = {
    val completed = DAO.getCompletedPathList(conn)
    if (completed.nonEmpty) {
      val grouped = completed
        .groupBy(_.version)
        .map(g1 => {
          g1._1 -> g1._2
            .groupBy(_.hardware)
            .map(g2 => {
              g2._1 -> g2._2
                .groupBy(_.src_filename)
                .map(g3 => {
                  g3._1 -> g3._2
                    .groupBy(_.workload)
                    .map(g4 => {
                      g4._1 -> g4._2
                    })
                })
            })
        })
      grouped.keySet.foreach(k => {
        println(s"* V: $k")
        grouped(k).foreach(p => {
          println(s"\t* HW: ${p._1}")
          p._2.foreach(p1 => {
            println(s"\t\t* Program: ${p1._1}")
            p1._2.foreach(p2 => {
              println(s"\t\t\t* w = ${p2._1} - ${p2._2.head.num_paths}")
            })
          })
        })
      })
    } else {
      println("N/A\n")
    }
  }

  private def printCompletedBenchmarks(conn: DBConnection): Unit = {
    val completed = DAO.getCompletedBenchmarks(conn)
    if (completed.nonEmpty) {
      val grouped = completed
        .groupBy(_.benchmark)
        .map(
          c1 =>
            c1._1 -> c1._2
              .groupBy(_.version)
              .map(c2 =>
                c2._1 -> c2._2.groupBy(_.hardware).map(c3 => c3._1 -> c3._2)))
      grouped.keySet.foreach(s => {
        println(s"* B: $s")
        grouped(s).foreach(p1 => {
          println(s"\t\t* V: ${p1._1}")
          p1._2.foreach(p2 => {
            val stressValues = p2._2.map(_.stress)
            println(
              s"\t\t\t\t* HW: ${p2._1} - w = [${stressValues.mkString(",")}]")
          })
        })
      })
    } else {
      println("N/A\n")
    }
  }

  private def printIncomplete(conn: DBConnection): Unit = {
    val metadata = DAO.getIncompleteMetadata(conn)

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
      println(s"* V: $k")
      structured(k).foreach(m => {
        println(
          "\t\t* HW: " + m._1 + s" — ${Math.round(m._2.head.percentCompleted * 10) / 10}%")
        println("\t\t\t* Errors:")
        m._2.head.errorMapping.foreach(em => {
          println(s"\t\t\t\t\t* ${em._1} — ${if (em._2 > 0) red(em._2.toString)
          else green(em._2.toString)}")
        })
      })
    })
  }
}
