package gvc.benchmarking

object BenchmarkExecutor {

  def execute(config: ExecutorConfig): Unit = {
    val dbConnection = DAO.connect(config.db)

    /*
   *   Assume we have a version string and a hardware string identifying our current platform, and a directory of example programs.
   *   0. Sync the directory of example programs with the database, identifying which match the current entries in the DB.
   *
   *   1. Query the database for the ID associated with the version and hardware strings. If it doesn't exist, add it.
   *
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
   *
   *
   *    Note: There are likely ways of creating "batches" of queries to execute in a single transaction using Doobie. This might be a better approach than listed
   *          in steps 1 through 3. Essentially, instead of executing queries one-by-one and dealing with the race condition between steps 1 and 3, perform one set
   *          of queries that identifies a permutation without performance data, reserves it in the database with placeholder data, and returns the data associated
   *          with the permutation. If this executes as a single transaction, it will block all other threads from performing database updates. So, we know that if
   *          this combined query fails, we need to generate new programs to benchmark.
   *
   *          To create this "combined query," we'll need to write each of the individual queries anyway, so feel free to follow steps 1-3 as written for now.
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
