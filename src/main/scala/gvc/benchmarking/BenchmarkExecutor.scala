package gvc.benchmarking

import gvc.CC0Wrapper.Performance
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType, Permutation}
import gvc.benchmarking.Timing.{CC0CompilationException, CC0ExecutionException}
import gvc.transformer.IRPrinter
import gvc.{Config, Main, VerificationException}

import java.nio.file.{Files, Paths}
import scala.concurrent.TimeoutException

object BenchmarkExecutor {

  case class ReservedProgram(perm: Permutation,
                             stress: Int,
                             perfID: Long,
                             measurementMode: DynamicMeasurementMode)

  def execute(config: ExecutorConfig, baseConfig: Config): Unit = {
    val conn = DAO.connect(config.db)
    val globalConfig = DAO.resolveGlobalConfiguration(conn)
    val storedVersion = DAO.addOrResolveVersion(config.version, conn)
    val storedHardware = DAO.addOrResolveHardware(config.hardware, conn)
    val libraries = Main.Defaults.includeDirectories

    val syncedPrograms =
      BenchmarkPopulator.syncPrograms(config.sources,
                                      libraries,
                                      globalConfig,
                                      conn)

    val workload = config.workload

    val tempBinary = Paths.get(Main.Defaults.outputFileCollection.binaryName)
    val tempSource = Paths.get(Main.Defaults.outputFileCollection.c0FileName)

    val worklist =
      BenchmarkExternalConfig.generateStressList(config.workload.stress)

    var reservedProgram =
      DAO.reserveProgramForMeasurement(storedVersion,
                                       storedHardware,
                                       worklist,
                                       conn)

    while (reservedProgram.nonEmpty) {

      val reserved = reservedProgram.get
      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).info.labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                              reserved.perm.permutationHash)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).info.ir).visit(asLabelSet)
      val reconstructedSourceText =
        IRPrinter.print(convertedToIR, includeSpecs = false)

      Files.writeString(tempSource, reconstructedSourceText)

      val timingStart = System.nanoTime()

      val benchmarkingFunction: () => Performance =
        reserved.measurementMode match {
          case DynamicMeasurementMode.Dynamic =>
            () =>
              {
                val ir = Main.generateIR(reconstructedSourceText, libraries)
                BaselineChecker.check(ir)
                Files.writeString(tempSource,
                                  IRPrinter.print(ir, includeSpecs = false))
                Timing.compileTimed(tempSource,
                                    tempBinary,
                                    baseConfig,
                                    workload.staticIterations)
                Timing.execTimed(tempBinary,
                                 workload.iterations,
                                 List(s"--stress=${reserved.stress}"))
              }
          case DynamicMeasurementMode.Framing =>
            () =>
              {
                val ir = Main.generateIR(reconstructedSourceText, libraries)
                BaselineChecker.check(ir, onlyFraming = true)
                Files.writeString(tempSource,
                                  IRPrinter.print(ir, includeSpecs = false))
                Timing.compileTimed(tempSource,
                                    tempBinary,
                                    baseConfig,
                                    workload.staticIterations)
                Timing.execTimed(tempBinary,
                                 workload.iterations,
                                 List(s"--stress=${reserved.stress}"))
              }
          case DynamicMeasurementMode.Gradual =>
            () =>
              {
                val vOut = Timing.verifyTimed(
                  reconstructedSourceText,
                  Main.Defaults.outputFileCollection,
                  baseConfig,
                  workload.staticIterations)

                Files.writeString(tempSource, vOut.output.c0Source)

                val cOut = Timing.compileTimed(tempSource,
                                               tempBinary,
                                               baseConfig,
                                               workload.staticIterations)

                DAO.updateStaticProfiling(storedVersion,
                                          storedHardware,
                                          reserved.perm.id,
                                          workload.staticIterations,
                                          vOut,
                                          cOut,
                                          conn)

                Timing.execTimed(tempBinary,
                                 workload.iterations,
                                 List(s"--stress=${reserved.stress}"))
              }
        }
      try {
        Timeout.runWithTimeout(globalConfig.timeoutMinutes * 60 * 1000)(
          benchmarkingFunction()) match {
          case Some(value) =>
            DAO.completeProgramMeasurement(reserved.perfID,
                                           workload.iterations,
                                           value,
                                           conn)
          case None =>
        }
      } catch {
        case t: Throwable =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong
          val (output: String, mode: DynamicMeasurementMode) = t match {
            case verify: VerificationException =>
              (verify.message, ErrorType.Verification)
            case compile: CC0CompilationException =>
              (compile.message, ErrorType.Compilation)
            case exec: CC0ExecutionException =>
              (exec.message, ErrorType.Execution)
            case _: TimeoutException =>
              ("", ErrorType.Timeout)
            case _ =>
          }
          DAO.logException(storedVersion,
                           storedHardware,
                           reserved,
                           mode,
                           output,
                           differenceSeconds,
                           conn)
      }
      reservedProgram = DAO.reserveProgramForMeasurement(storedVersion,
                                                         storedHardware,
                                                         worklist,
                                                         conn)
    }
  }
}
