package gvc.benchmarking

import gvc.benchmarking.DAO.DBConnection
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

    Output.title("Completed Programs")
    printCompletedPrograms(conn)

    Output.title("Completed Paths")
    printCompletedPaths(conn)

    Output.title("Completed Benchmarks")
    printCompletedBenchmarks(conn)

  }

  private def printCompletedPrograms(conn: DBConnection): Unit = {
    val completed = DAO.getCompletedProgramList(conn)
    if (completed.nonEmpty) {
      completed
        .groupBy(_.versionName)
        .foreach(g1 => {
          println(s"* V: ${g1._1}")
          g1._2
            .groupBy(_.hwName)
            .foreach(g2 => {
              println(s"\t* HW: ${g2._1}")
              g2._2
                .groupBy(_.stress)
                .foreach(g3 => {
                  println(s"\t\t* w = ${g3._1}")
                  g3._2
                    .groupBy(_.measurementType)
                    .foreach(g4 => {
                      val elem = g4._2.head
                      val completionPercentage = Math.round(
                        ((elem.completed.toDouble / elem.total) * 100) * 100) / 100
                      val errorPercentage = Math.round(
                        ((elem.errored.toDouble / elem.total) * 100) * 100) / 100
                      val errorColoring: String => String =
                        if (elem.errored == 0) green else red
                      println(s"\t\t\t* ${g4._1}: ${
                        green(
                          completionPercentage.toString + "%")
                      }, (${elem.completed} total) - ${
                        errorColoring(
                          errorPercentage.toString + "%")
                      }, (${elem.errored} total)")
                    })
                })
            })
        })
    } else {
      println("N/A\n")
    }
  }

  private def printCompletedPaths(conn: DBConnection): Unit = {
    val completed = DAO.getCompletedPathList(conn)
    if (completed.nonEmpty) {
      completed
        .groupBy(_.version)
        .foreach(g1 => {
          println(s"* V: ${g1._1}")
          g1._2
            .groupBy(_.hardware)
            .foreach(g2 => {
              println(s"\t* HW: ${g2._1}")
              g2._2
                .groupBy(_.src_filename)
                .foreach(g3 => {
                  println(s"\t\t* Program: ${g3._1}")
                  g3._2
                    .groupBy(_.workload)
                    .foreach(g4 => {
                      println(s"\t\t\t* w = ${g4._1}")
                      g4._2
                        .groupBy(_.measurementMode)
                        .foreach(g5 => {
                          println(
                            s"\t\t\t\t* ${g5._1}: ${g5._2.head.num_paths}")
                        })
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
      completed
        .groupBy(_.benchmark)
        .foreach(c1 => {
          println(s"* B: ${c1._1}")
          c1._2
            .groupBy(_.version)
            .foreach(c2 => {
              println(s"\t* V: ${c2._1}")
              c2._2
                .groupBy(_.hardware)
                .foreach(c3 => {
                  println(s"\t\t* HW: ${c3._1}")
                  c3._2
                    .groupBy(_.measurementMode)
                    .foreach(c4 => {
                      println(
                        s"\t\t\t* ${c4._1}: (${c4._2.map(_.stress).mkString(",")})")
                    })
                })
            })
        })
    } else {
      println("N/A\n")
    }
  }
}
