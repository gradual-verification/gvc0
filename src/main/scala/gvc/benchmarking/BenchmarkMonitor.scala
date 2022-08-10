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

    Output.title("Completed Mass Benchmarks")
    printCompletedPaths(conn)

    Output.title("Completed Preconfigured Benchmarks")
    printCompletedBenchmarks(conn)

  }

  private def printCompletedPrograms(conn: DBConnection): Unit = {
    val completed = DAO.getCompletedProgramList(conn)
    if (completed.nonEmpty) {
      val grouped = completed
        .groupBy(_.versionName)
        .map(g1 => {
          g1._1 -> g1._2
            .groupBy(_.hwName)
            .map(g2 => {
              g2._1 -> g2._2
                .groupBy(_.stress)
                .map(g3 => {
                  g3._1 -> g3._2
                    .groupBy(_.measurementType)
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
          val m = p._2
          m.foreach(p1 => {
            println(s"\t\t* w = ${p1._1}")
            val m2 = p1._2
            m2.foreach(p2 => {
              val elem = p2._2.head
              val completionPercentage = Math.round(
                ((elem.completed.toDouble / elem.total) * 100) * 100) / 100
              val errorPercentage = Math.round(
                ((elem.errored.toDouble / elem.total) * 100) * 100) / 100
              println(s"\t\t\t* ${p2._1}: ${green(
                completionPercentage.toString + "%")}, (${elem.completed} total) - ${red(
                errorPercentage.toString + "%")}, (${elem.errored} total)")
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
                        .groupBy(_.measurementMode)
                        .map(g5 => {
                          g5._1 -> g5._2
                        })
                    })
                })
            })
        })
      grouped.keySet.foreach(k => {
        println(s"* V: $k")
        grouped(k).foreach(p => {
          println(s"\t* HW: ${p._1}")
          val m = p._2
          m.foreach(p1 => {
            println(s"\t\t* Program: ${p1._1}")
            val m2 = p1._2
            m2.foreach(p2 => {
              println(s"\t\t\t* w = ${p2._1}")
              val m3 = p2._2
              m3.foreach(p3 => {
                println(s"\t\t\t\t* ${p3._1}: ${p3._2.head.num_paths}")
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
      val grouped = completed
        .groupBy(_.benchmark)
        .map(
          c1 =>
            c1._1 -> c1._2
              .groupBy(_.version)
              .map(c2 =>
                c2._1 -> c2._2
                  .groupBy(_.hardware)
                  .map(c3 => {
                    c3._1 -> c3._2
                      .groupBy(_.measurementMode)
                      .map(c4 => {
                        c4._1 -> c4._2
                      })
                  })))

      grouped.keySet.foreach(s => {
        println(s"* B: $s")
        grouped(s).foreach(p => {
          println(s"\t* V: ${p._1}")
          p._2.foreach(p1 => {
            println(s"\t\t* HW: ${p1._1}")
            p1._2.foreach(p2 => {
              println(
                s"\t\t\t* ${p2._1}: (${p2._2.map(_.stress).mkString(",")})")
            })
          })
        })
      })
    } else {
      println("N/A\n")
    }
  }
}
