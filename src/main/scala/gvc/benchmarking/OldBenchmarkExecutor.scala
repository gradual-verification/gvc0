package gvc.benchmarking
import gvc.benchmarking.DAO.Permutation
object OldBenchmarkExecutor {
  case class ReservedProgram(perm: Permutation,
                             workloads: List[Int],
                             measurementMode: Long)

  /*
  def execute(config: ExecutorConfig,
              baseConfig: Config,
              libraries: List[String]): Unit = {

    val conn = DAO.connect(config.db)
    val globalConfig = DAO.resolveGlobalConfiguration(conn)
    val id = DAO.addOrResolveIdentity(config, conn)
    val modes = DAO.resolveDynamicModes(conn)
    var currentSiliconInstance: Option[Silicon] = None
    val ongoingProcesses = mutable.ListBuffer[scala.sys.process.Process]()

    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)

    val stressEntries =
      this.createTemporaryStressEntries(syncedPrograms, config.workload)

    val workload = config.workload



    var reservedProgram =
      DAO.reserveProgramForMeasurement(id, stressEntries, conn)









    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${modes(
          reserved.measurementMode)} | w=[${reserved.workloads
          .mkString(",")}] | id=${reserved.perm.id}")



      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir).visit(asLabelSet)

      val binaryToExecute = modes.get(reserved.measurementMode) match {
        case Some(value) =>
          value match {
            case DynamicMeasurementMode.Dynamic |
                DynamicMeasurementMode.Framing =>
              benchmarkBaseline(convertedToIR,
                                value == DynamicMeasurementMode.Framing)
            case DynamicMeasurementMode.Gradual =>
              benchmarkGradual(convertedToIR, reserved)
          }
        case None =>
          error(
            s"Unrecognized dynamic measurement mode with ID ${reserved.measurementMode}")
      }
      binaryToExecute match {
        case Some(value) =>
          reserved.workloads
            .foreach(w => {
              val perfOption = wrapTiming(
                Timing.execTimed(value,
                                 List(s"--stress $w"),
                                 config.workload.iterations,
                                 ongoingProcesses))
              perfOption match {
                case Left(t) => reportError(reserved, t)
                case Right(p) =>
                  DAO.completeProgramMeasurement(id,
                                                 reserved,
                                                 w,
                                                 config.workload.iterations,
                                                 p,
                                                 conn)
              }

            })
        case None =>
      }
      reservedProgram =
        DAO.reserveProgramForMeasurement(id, stressEntries, conn)
    }
  }*/

  case class WorkloadEntry(programID: Long, workloadValue: Int)

}
