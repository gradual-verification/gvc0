package gvc.benchmarking

import gvc.{Config}

object BenchmarkExecutor {

  def execute(config: ExecutorConfig, baseConfig: Config): Unit = {
    val conn = DAO.connect(config.db)
    val storedVersion = DAO.addOrResolveVersion(config.version, conn)
    val storedHardware = DAO.addOrResolveHardware(config.hardware, conn)
    
    val workload = config.workload
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
