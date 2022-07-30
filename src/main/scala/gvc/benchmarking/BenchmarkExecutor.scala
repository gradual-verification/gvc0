package gvc.benchmarking

import gvc.CC0Wrapper.{CommandOutput, Performance}
import gvc.Config.error
import gvc.benchmarking.Benchmark.{
  BenchmarkException,
  injectStress,
  isInjectable
}
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType, Permutation}
import gvc.benchmarking.Timing.{CC0CompilationException, CC0ExecutionException}
import gvc.transformer.IRPrinter
import gvc.weaver.WeaverException
import gvc.{Config, Main, VerificationException}

import java.nio.file.{Files, Path, Paths}
import scala.concurrent.TimeoutException

object BenchmarkExecutor {
  def injectAndWrite(c0: String, dest: Path): Unit = {
    if (!isInjectable(c0)) {
      throw new BenchmarkException(
        s"The file doesn't include an assignment of the form 'int stress = ...'."
      )
    }
    val source = injectStress(c0)
    Files.writeString(
      dest,
      source
    )
  }

  case class ReservedProgram(perm: Permutation,
                             stress: Int,
                             measurementMode: Long)

  def execute(config: ExecutorConfig,
              baseConfig: Config,
              libraries: List[String]): Unit = {

    val conn = DAO.connect(config.db)
    val globalConfig = DAO.resolveGlobalConfiguration(conn)
    val id = DAO.addOrResolveIdentity(config, conn)
    val modes = DAO.resolveDynamicModes(conn)

    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)

    val workload = config.workload

    val tempBinary =
      Files.createTempFile("temp_bin", ".c0")

    val tempSource = Files.createTempFile("temp_src", ".c0")

    val worklist =
      BenchmarkExternalConfig.generateStressList(config.workload.stress)

    var reservedProgram =
      DAO.reserveProgramForMeasurement(id, worklist, conn)

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${modes(
          reserved.measurementMode)} | w=${reserved.stress} | id=${reserved.perm.id}")

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                              reserved.perm.permutationHash)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir).visit(asLabelSet)

      val timingStart = System.nanoTime()

      val benchmarkingFunction: () => Performance =
        modes.get(reserved.measurementMode) match {
          case Some(value) =>
            value match {
              case DynamicMeasurementMode.Dynamic =>
                () =>
                  {
                    BaselineChecker.check(convertedToIR)
                    val sourceText =
                      IRPrinter.print(convertedToIR, includeSpecs = false)
                    this.injectAndWrite(sourceText, tempSource)
                    Files.deleteIfExists(tempBinary)
                    throw new CC0ExecutionException(CommandOutput(0, "hello"))
                    Timing.compileTimed(tempSource,
                                        tempBinary,
                                        baseConfig,
                                        workload.staticIterations)
                    Timing.execTimed(tempBinary,
                                     workload.iterations,
                                     List(s"--stress ${reserved.stress}"))
                  }
              case DynamicMeasurementMode.Framing =>
                () =>
                  {
                    BaselineChecker.check(convertedToIR, onlyFraming = true)
                    val sourceText =
                      IRPrinter.print(convertedToIR, includeSpecs = false)
                    this.injectAndWrite(sourceText, tempSource)
                    Files.writeString(
                      tempSource,
                      IRPrinter.print(convertedToIR, includeSpecs = false))
                    Files.deleteIfExists(tempBinary)
                    Timing.compileTimed(tempSource,
                                        tempBinary,
                                        baseConfig,
                                        workload.staticIterations)
                    Timing.execTimed(tempBinary,
                                     workload.iterations,
                                     List(s"--stress ${reserved.stress}"))
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

                    if (!isInjectable(vOut.output.c0Source)) {
                      throw new BenchmarkException(
                        s"The file doesn't include an assignment of the form 'int stress = ...'."
                      )
                    }
                    val source = injectStress(vOut.output.c0Source)
                    Files.writeString(tempSource, source)
                    Files.deleteIfExists(tempBinary)

                    val cOut = Timing.compileTimed(tempSource,
                                                   tempBinary,
                                                   baseConfig,
                                                   workload.staticIterations)
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
          case None =>
            error(
              s"Unrecognized dynamic measurement mode with ID ${reserved.measurementMode}")
        }

      try {
        val performanceResult =
          Timeout.runWithTimeout(globalConfig.timeoutMinutes * 60 * 1000)(
            benchmarkingFunction())
        DAO.completeProgramMeasurement(id,
                                       reserved,
                                       workload.iterations,
                                       performanceResult,
                                       conn)
      } catch {
        case t: Throwable =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong

          val errorType = t match {
            case _: TimeoutException        => ErrorType.Timeout
            case _: VerificationException   => ErrorType.Verification
            case _: CC0CompilationException => ErrorType.Compilation
            case _: CC0ExecutionException   => ErrorType.Execution
            case _: WeaverException         => ErrorType.Weaving
            case _                          => ErrorType.Unknown
          }
          DAO.logException(id,
                           reserved,
                           errorType,
                           t.getMessage,
                           differenceSeconds,
                           conn)

      }
      reservedProgram = DAO.reserveProgramForMeasurement(id, worklist, conn)
    }
  }
}
