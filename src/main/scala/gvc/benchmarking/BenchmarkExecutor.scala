package gvc.benchmarking

import gvc.Config

object BenchmarkExecutor {
  /**
   *
   * @param config
     1. Grab a program from the database that doesn't have performance results for the current HWID and VID
     2. Insert a placeholder result for that program: If another node has already inserted the result,
          Query will fail
     3. If fail then go to step one
   */
  def execute(config: Config): Unit =
  {
    // transactor from DAO is the executer script
  }

}
