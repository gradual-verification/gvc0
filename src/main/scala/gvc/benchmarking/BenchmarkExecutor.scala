package gvc.benchmarking

import gvc.benchmarking.DAO.Permutation
import gvc.{Config, Main}

import java.nio.file.{Files, Paths}

object BenchmarkExecutor {

  case class ReservedProgram(perm: Permutation, stress: Int)

  def execute(config: ExecutorConfig, baseConfig: Config): Unit = {
    val conn = DAO.connect(config.db)
    val storedVersion = DAO.addOrResolveVersion(config.version, conn)
    val storedHardware = DAO.addOrResolveHardware(config.hardware, conn)
    val libraries = List(Main.defaultLibraryDirectory)
    val syncedPrograms =
      BenchmarkPopulator.syncPrograms(config.sources, libraries, conn)
    val workload = config.workload
    val tempBinary = Paths.get(Main.tempOutputCollection.binaryName)
    val tempSource = Paths.get(Main.tempOutputCollection.c0FileName)
    var reservedProgram =
      DAO.reserveProgram(storedVersion, storedHardware, config.workload, conn)

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      val reconstructedSourceText = ""
      Files.writeString(tempSource, reconstructedSourceText)
      val verifierOutput = Timing.verifyTimed(reconstructedSourceText,
                                              Main.tempOutputCollection,
                                              baseConfig)
      val compilationOutput = Timing.compileTimed(tempSource,
                                                  tempBinary,
                                                  baseConfig,
                                                  workload.iterations)
      val executionOutput =
        Timing.execTimed(tempBinary,
                         workload.iterations,
                         List(s"--stress=${reserved.stress}"))

      reservedProgram =
        DAO.reserveProgram(storedVersion, storedHardware, config.workload, conn)
    }

    /*



   *   Assume we have a version string and a hardware string identifying our current platform, and a directory of example programs.
   *   2. Find a permutation of a program that we have locally that doesn't have an associated entry in the performance table matching the hardware and version ID.
   *       * If none exists, attempt to generate new paths/programs until one does.
   *
   *   3. Update the performance table with an entry containing the version and hardware ID, but with N/A or NULL for the performance metrics
   *       * this effectively "reserves" this particular program for this script to benchmark, preventing multiple BenchmarkExecutors from repeating work.
   *       * If the update fails, another benchmark script got here first between step 1 and 3. Return to step 1.
   *
   *   4. Using the permutation's ID and the program that it came from, recreate the permutation as a C0 file. (I can assist with this).
   *
   *   5. Benchmark (verify, execute) the C0 file and record results.



   *
   *   6. Update the permutation's entry in the performance table with the results. Return to step 1.
   * */
  }

  /**
  *
  * @param config
  * 1. Grab a program from the database that doesn't have performance results for the current HWID and VID
  * 2. Insert a placeholder result for that program: If another node has already inserted the result,
  * Query will fail
  * 3. If fail then go to step one
  */

}
