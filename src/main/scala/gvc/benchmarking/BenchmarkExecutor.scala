package gvc.benchmarking

import gvc.Config.error
import gvc.Main.writeFile
import gvc.benchmarking.BenchmarkCommon.{
  BenchmarkException,
  injectStress,
  isInjectable
}
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType, Permutation}
import gvc.benchmarking.Timing.{
  CC0CompilationException,
  CC0ExecutionException,
  TimedVerification
}
import gvc.transformer.{IR, IRPrinter}
import gvc.weaver.WeaverException
import gvc.{Config, Main, VerificationException}
import viper.silicon.Silicon

import java.nio.file.{Files, Path}
import java.util.Calendar
import scala.collection.mutable
import scala.concurrent.TimeoutException
import scala.reflect.io.Directory

object BenchmarkExecutor {

  case class VerificationTimeoutException(timeout: Throwable)
      extends Exception(timeout.getMessage)

  class SiliconState(config: Config) {
    private var currentInstance: Option[Silicon] = None

    def trackInstance(silicon: Silicon): Unit = {
      this.currentInstance match {
        case Some(value) => value.stop()
        case None        =>
      }
      this.currentInstance = Some(silicon)
    }

    def verifyWithTimeout(
        permutationID: Long,
        source: String,
        minutes: Int
    ): Either[Throwable, TimedVerification] = {
      try {
        val res = Timeout.runWithTimeout(minutes * 60 * 1000)(
          Timing.verifyTimed(
            SiliconState.this,
            source,
            Main.Defaults.outputFileCollection,
            config
          )
        )
        Right(res)
      } catch {
        case t: Throwable =>
          this.currentInstance match {
            case Some(value) => value.stop()
            case None        =>
          }
          Output.error(f"Error in permutation $permutationID: ${t.getMessage}")
          Left(VerificationTimeoutException(t))
      }
    }
  }

  case class ReservedProgram(
      perm: Permutation,
      workloads: List[Int],
      measurementMode: Long
  )

  def execute(
      config: ExecutorConfig,
      baseConfig: Config,
      libraries: List[String]
  ): Unit = {
    if (config.modifiers.onlyBenchmark) {
      Output.info(s"Targeting ${Output.blue("benchmarks")}.")
    } else {
      Output.info(s"Targeting ${Output.blue("all programs")}.")
    }

    config.modifiers.exclusiveMode match {
      case Some(value) =>
        Output.info(s"Exclusive verification mode: ${Output.blue(value)}")
      case None =>
    }
    Output.info(
      s"Timeout: ${Output.blue(config.timeoutMinutes.toString)} minutes."
    )
    Output.info(
      s"Iterations: ${Output.blue(config.workload.iterations.toString)}"
    )
    Output.info(
      s"Nickname sensitivity: ${Output.flag(config.modifiers.nicknameSensitivity)}."
    )
    Output.info(
      s"Profiling: ${Output.flag(config.profilingDirectory.nonEmpty)}."
    )

    val conn = DAO.connect(config.db)
    val id = DAO.addOrResolveIdentity(config, conn)
    val stressTable = new StressTable(config.workload)
    val silicon = new SiliconState(baseConfig)
    val ongoingProcesses = mutable.ListBuffer[scala.sys.process.Process]()
    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)

    val tempBinary =
      Files.createTempFile("temp_bin", ".out")

    val tempSource =
      Files.createTempFile("temp_src", ".c0")

    var reservedProgram =
      DAO.reserveProgramForMeasurement(id, stressTable, config, conn)

    config.profilingDirectory match {
      case Some(value) =>
        if (Files.exists(value)) new Directory(value.toFile).deleteRecursively()
        Files.createDirectory(value)
      case None =>
    }

    def reportError(
        src: String,
        reserved: ReservedProgram,
        t: Throwable
    ): Unit = {

      val typeToReport = t match {
        case _: VerificationException        => ErrorType.Verification
        case _: CC0CompilationException      => ErrorType.Compilation
        case _: CC0ExecutionException        => ErrorType.Execution
        case _: VerificationTimeoutException => ErrorType.VerificationTimeout
        case _: TimeoutException             => ErrorType.ExecutionTimeout
        case _: WeaverException              => ErrorType.Weaving
        case _                               => ErrorType.Unknown
      }

      config.modifiers.saveErroredPerms match {
        case Some(value) =>
          val errPath = value.resolve(
            BenchmarkCommon.Extensions.c0(
              s"errored_${typeToReport}_${reserved.perm.programID}_${reserved.perm.id}"
            )
          )
          writeFile(errPath.toString, src)
        case None =>
      }

      val resolved = DAO.resolveException(typeToReport, t.getMessage, conn)
      typeToReport match {
        case ErrorType.Verification | ErrorType.Compilation |
            ErrorType.Weaving | ErrorType.VerificationTimeout =>
          DAO.logStaticException(id, reserved, resolved, conn)
        case ErrorType.ExecutionTimeout =>
          DAO.logDynamicException(
            id,
            reserved,
            resolved,
            reserved.workloads,
            conn
          )
        case ErrorType.Unknown =>
          DAO.logStaticException(id, reserved, resolved, conn)
          DAO.logDynamicException(
            id,
            reserved,
            resolved,
            reserved.workloads,
            conn
          )
        case ErrorType.Execution =>
          val stress = t match {
            case c: CC0ExecutionException => List(c.getStress)
            case _                        => reserved.workloads
          }
          DAO.logDynamicException(id, reserved, resolved, stress, conn)
      }
    }

    def benchmarkGradual(
        ir: IR.Program,
        reserved: ReservedProgram
    ): Option[Path] = {
      val (verifiedSource, verifierOutput): (
          String,
          Option[TimedVerification]
      ) =
        DAO.resolveVerifiedPermutation(id.vid, reserved.perm.id, conn) match {
          case Some(value) => (value, None)
          case None =>
            val reconstructedSourceText =
              IRPrinter.print(ir, includeSpecs = true)
            val vOut = silicon.verifyWithTimeout(
              reserved.perm.id,
              reconstructedSourceText,
              config.timeoutMinutes
            )
            vOut match {
              case Left(t) =>
                reportError(reconstructedSourceText, reserved, t)
                return None
              case Right(value) =>
                (value.output.c0Source, Some(value))
            }
        }
      if (!isInjectable(verifiedSource)) {
        throw new BenchmarkException(
          s"The file doesn't include an assignment of the form 'int stress = ...'."
        )
      }
      val injectedSource = injectStress(verifiedSource)
      Files.writeString(tempSource, injectedSource)
      Files.deleteIfExists(tempBinary)

      val cOut = Timing.compileTimed(
        tempSource,
        tempBinary,
        baseConfig,
        config.workload.staticIterations,
        config.profilingDirectory.nonEmpty,
        ongoingProcesses
      )

      verifierOutput match {
        case Some(value) =>
          DAO.updateStaticProfiling(
            id,
            reserved.perm.id,
            config.workload.staticIterations,
            value,
            cOut,
            conn
          )
        case None =>
      }

      Some(tempBinary)
    }

    def benchmarkBaseline(
        ir: IR.Program,
        onlyFraming: Boolean
    ): Option[Path] = {
      BaselineChecks.insert(ir, true, !onlyFraming)
      val sourceText =
        IRPrinter.print(ir, includeSpecs = false)

      this.injectAndWrite(sourceText, tempSource)
      Files.deleteIfExists(tempBinary)
      Timing.compileTimed(
        tempSource,
        tempBinary,
        baseConfig,
        config.workload.staticIterations,
        config.profilingDirectory.nonEmpty,
        ongoingProcesses
      )

      Some(tempBinary)
    }

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get

      val cal = Calendar.getInstance()
      val currentTime =
        s"${cal.get(Calendar.HOUR_OF_DAY)}:${cal.get(Calendar.MINUTE)}:${cal.get(Calendar.SECOND)}"

      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${conn
          .dynamicModes(reserved.measurementMode)} | w=[${reserved.workloads
          .mkString(",")}] | id=${reserved.perm.id} | $currentTime"
      )

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(
          correspondingProgramLabels,
          reserved.perm.permutationContents
        )

      val convertedToIRTemp = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir
      ).visit(asLabelSet)

      val reconstructedSourceText =
        IRPrinter.print(convertedToIRTemp, includeSpecs = true)

      // Hacky solution for issue 59; since SelectVisitor produces an IR that BaselineChecker can't
      // use correctly. The IR produces a correct source program though.
      // Solution: recreate IR from reconstructedSourceText (aka text from IR generated from perm in SelectVisitor)
      // Use this fresh IR for verification
      val convertedToIR = Main.generateIR(reconstructedSourceText, libraries)

      conn.dynamicModes.get(reserved.measurementMode) match {
        case Some(mode) =>
          val binary = mode match {
            case DynamicMeasurementMode.Dynamic |
                DynamicMeasurementMode.Framing =>
              benchmarkBaseline(
                convertedToIR,
                mode == DynamicMeasurementMode.Framing
              )
            case DynamicMeasurementMode.Gradual =>
              benchmarkGradual(convertedToIR, reserved)
          }
          binary match {
            case Some(binaryToExecute) =>
              reserved.workloads
                .foreach(w => {
                  val profiler =
                    resolveProfiler(config, reserved, binaryToExecute, mode, w)
                  val perfOption =
                    try {
                      Right(
                        Timeout.runWithTimeout(
                          config.timeoutMinutes * 60 * 1000
                        )(
                          Timing.execTimed(
                            binaryToExecute,
                            List(),
                            config.workload.iterations,
                            w,
                            ongoingProcesses,
                            profiler
                          )
                        )
                      )
                    } catch {
                      case t: Throwable =>
                        while (ongoingProcesses.nonEmpty) {
                          val process = ongoingProcesses.remove(0)
                          if (process.isAlive) process.destroy()
                        }
                        Output.error(
                          s"Error with Perm ID= ${reserved.perm.id}: " + t.getMessage
                        )
                        Left(t)
                    }
                  perfOption match {
                    case Left(t) =>
                      reportError(reconstructedSourceText, reserved, t)
                    case Right(p) =>
                      profiler match {
                        case Some(value) => value.complete()
                        case None        =>
                      }
                      
                      DAO.completeProgramMeasurement(
                        id,
                        reserved,
                        w,
                        config.workload.iterations,
                        p,
                        conn
                      )
                  }
                })

            case None =>
          }
        case None =>
          error(
            s"Unrecognized dynamic measurement mode with ID ${reserved.measurementMode}"
          )
      }
      reservedProgram =
        DAO.reserveProgramForMeasurement(id, stressTable, config, conn)
    }
    Output.info("No additional permutations available for reservation.")
  }

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

  def resolveProfiler(
      config: ExecutorConfig,
      reservedProgram: ReservedProgram,
      binary: Path,
      measurementMode: DynamicMeasurementMode,
      workload: Int
  ): Option[GProf] = {
    config.profilingDirectory match {
      case Some(value) =>
        val filename = BenchmarkCommon.Extensions.txt(
          s"${measurementMode}_${workload}_${reservedProgram.perm.programID}_${reservedProgram.perm.id}"
        )
        val sumPath = value.resolve(filename)
        Some(new GProf(binary, sumPath))
      case None => None
    }
  }

  class StressTable(workload: BenchmarkWorkload) {
    private val defaultStressValues = workload.stress match {
      case Some(value) => BenchmarkExternalConfig.generateStressList(value)
      case None        => List.empty[Int]
    }
    private val userConfiguredStressValues = workload.programCases
      .flatMap(c => {
        val stressValues =
          BenchmarkExternalConfig.generateStressList(c.workload)
        for {
          i1: String <- c.matches
        } yield i1 -> stressValues
      })
      .toMap

    def get(filename: String): List[Int] = {
      val stressList =
        userConfiguredStressValues.getOrElse(filename, defaultStressValues)
      stressList
    }
  }

}
