package gvc.benchmarking

import gvc.CC0Wrapper.{CommandOutput, Performance}
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType, Permutation}
import gvc.benchmarking.Timing.{
  CC0CompilationException,
  CC0ExecutionException,
  CapturedOutputException
}
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
    val id = DAO.addOrResolveIdentity(config, conn)
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
      DAO.reserveProgramForMeasurement(id, worklist, conn)

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).info.fileName} | ${reserved.measurementMode} | w=${reserved.stress} | id=${reserved.perm.permutationHash}")

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).info.labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                              reserved.perm.permutationHash)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).info.ir).visit(asLabelSet)

      val timingStart = System.nanoTime()

      val benchmarkingFunction: () => Performance =
        reserved.measurementMode match {
          case DynamicMeasurementMode.Dynamic =>
            () =>
              {
                BaselineChecker.check(convertedToIR)
                Files.writeString(
                  tempSource,
                  IRPrinter.print(convertedToIR, includeSpecs = false))
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
                BaselineChecker.check(convertedToIR, onlyFraming = true)
                Files.writeString(
                  tempSource,
                  IRPrinter.print(convertedToIR, includeSpecs = false))
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
                val reconstructedSourceText =
                  IRPrinter.print(convertedToIR, includeSpecs = true)
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
                throw new CC0CompilationException(CommandOutput(1, "hello"))
                DAO.updateStaticProfiling(id,
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
        case _: TimeoutException =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong
          DAO.logException(id,
                           reserved,
                           ErrorType.Timeout,
                           "",
                           differenceSeconds,
                           conn)
        case vex: VerificationException =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong
          DAO.logException(id,
                           reserved,
                           ErrorType.Verification,
                           vex.message,
                           differenceSeconds,
                           conn)

        case coe: CapturedOutputException =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong
          val eType = coe match {
            case _: CC0CompilationException => ErrorType.Compilation
            case _: CC0ExecutionException   => ErrorType.Execution
          }
          DAO.logException(id,
                           reserved,
                           eType,
                           coe.message,
                           differenceSeconds,
                           conn)
      }
      reservedProgram = DAO.reserveProgramForMeasurement(id, worklist, conn)
    }
  }
}
