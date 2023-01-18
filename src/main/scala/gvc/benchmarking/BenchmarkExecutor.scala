package gvc.benchmarking

import gvc.Config.error
import gvc.Main.{resolveSilicon, writeFile}
import gvc.benchmarking.Benchmark.{
  BenchmarkException,
  injectStress,
  isInjectable
}
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

object BenchmarkExecutor {

  case class VerificationTimeoutException(timeout: Throwable)
    extends Exception(timeout.getMessage)

  class SiliconState(config: Config) {
    private var currentSiliconInstance: Option[Silicon] = None

    private def init(): Silicon = {
      val newInstance = resolveSilicon(config)
      currentSiliconInstance = Some(newInstance)
      newInstance
    }

    private def destroy(): Unit = {
      currentSiliconInstance match {
        case Some(value) => value.stop()
        case None =>
      }
      currentSiliconInstance = None
    }

    def verify(permutationID: Long,
               source: String,
               minutes: Int): Either[Throwable, TimedVerification] = {
      currentSiliconInstance.synchronized {
        this.currentSiliconInstance match {
          case None =>
            val instance = this.init()
            try {
              val res = Timeout.runWithTimeout(minutes * 60 * 1000)(
                Timing.verifyTimed(instance,
                  source,
                  Main.Defaults.outputFileCollection,
                  config)
              )
              this.destroy()
              Right(res)
            } catch {
              case t: Throwable =>
                this.destroy()
                Output.error(
                  f"Error in permutation $permutationID: ${t.getMessage}")
                Left(VerificationTimeoutException(t))
            }
          case Some(_) =>
            error("Cannot begin verification before prior run has terminated.")
        }
      }
    }
  }

  case class ReservedProgram(perm: Permutation,
                             workloads: List[Int],
                             measurementMode: Long)

  def execute(config: ExecutorConfig,
              baseConfig: Config,
              libraries: List[String]): Unit = {
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
      s"Timeout: ${Output.blue(config.timeoutMinutes.toString)} minutes.")
    Output.info(
      s"Iterations: ${Output.blue(config.workload.iterations.toString)}")
    Output.info(
      s"Nickname sensitivity: ${Output.flag(config.modifiers.nicknameSensitivity)}.")

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

    def reportError(src: String,
                    reserved: ReservedProgram,
                    t: Throwable): Unit = {

      val typeToReport = t match {
        case _: VerificationException => ErrorType.Verification
        case _: CC0CompilationException => ErrorType.Compilation
        case _: CC0ExecutionException => ErrorType.Execution
        case _: VerificationTimeoutException => ErrorType.VerificationTimeout
        case _: TimeoutException => ErrorType.ExecutionTimeout
        case _: WeaverException => ErrorType.Weaving
        case _ => ErrorType.Unknown
      }

      config.modifiers.saveErroredPerms match {
        case Some(value) =>
          val errPath = value.resolve(Benchmark.Extensions.c0(
            s"errored_${typeToReport}_${reserved.perm.programID}_${reserved.perm.id}"))
          writeFile(errPath.toString, src)
        case None =>
      }

      val resolved = DAO.resolveException(typeToReport, t.getMessage, conn)
      typeToReport match {
        case ErrorType.Verification | ErrorType.Compilation |
             ErrorType.Weaving | ErrorType.VerificationTimeout =>
          DAO.logStaticException(id, reserved, resolved, conn)
        case ErrorType.ExecutionTimeout =>
          DAO.logDynamicException(id,
            reserved,
            resolved,
            reserved.workloads,
            conn)
        case ErrorType.Unknown =>
          DAO.logStaticException(id, reserved, resolved, conn)
          DAO.logDynamicException(id,
            reserved,
            resolved,
            reserved.workloads,
            conn)
        case ErrorType.Execution =>
          val stress = t match {
            case c: CC0ExecutionException => List(c.getStress)
            case _ => reserved.workloads
          }
          DAO.logDynamicException(id, reserved, resolved, stress, conn)
      }
    }

    def benchmarkGradual(ir: IR.Program,
                         reserved: ReservedProgram): Option[Path] = {
      val reconstructedSourceText =
        IRPrinter.print(ir, includeSpecs = true)

      val vOut = silicon.verify(reserved.perm.id,
        reconstructedSourceText,
        config.timeoutMinutes)

      vOut match {
        case Left(t) =>
          reportError(reconstructedSourceText, reserved, t)
          None
        case Right(verified) =>
          if (!isInjectable(verified.output.c0Source)) {
            throw new BenchmarkException(
              s"The file doesn't include an assignment of the form 'int stress = ...'."
            )
          }
          val source = injectStress(verified.output.c0Source)
          Files.writeString(tempSource, source)
          Files.deleteIfExists(tempBinary)

          val cOut = Timing.compileTimed(tempSource,
            tempBinary,
            baseConfig,
            config.workload.staticIterations,
            ongoingProcesses)
          DAO.updateStaticProfiling(id,
            reserved.perm.id,
            config.workload.staticIterations,
            verified,
            cOut,
            conn)
          Some(tempBinary)
      }
    }

    def benchmarkBaseline(ir: IR.Program,
                          onlyFraming: Boolean): Option[Path] = {
      BaselineChecker.check(ir, onlyFraming)
      val sourceText =
        IRPrinter.print(ir, includeSpecs = false)
      this.injectAndWrite(sourceText, tempSource)
      Files.deleteIfExists(tempBinary)
      Timing.compileTimed(tempSource,
        tempBinary,
        baseConfig,
        config.workload.staticIterations,
        ongoingProcesses)
      Some(tempBinary)
    }

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get

      val cal = Calendar.getInstance()
      val currentTime =
        s"${cal.get(Calendar.HOUR_OF_DAY)}:${cal.get(Calendar.MINUTE)}:${cal.get(Calendar.SECOND)}"

      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${
          conn
            .dynamicModes(reserved.measurementMode)
        } | w=[${
          reserved.workloads
            .mkString(",")
        }] | id=${reserved.perm.id} | $currentTime")

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
          reserved.perm.permutationContents)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir).visit(asLabelSet)

      val reconstructedSourceText = IRPrinter.print(convertedToIR, includeSpecs = true)

      val binaryToExecute =
        conn.dynamicModes.get(reserved.measurementMode) match {
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
              val perfOption = try {
                Right(
                  Timeout.runWithTimeout(config.timeoutMinutes * 60 * 1000)(
                    Timing.execTimed(value,
                      List(),
                      config.workload.iterations,
                      w,
                      ongoingProcesses)))
              } catch {
                case t: Throwable =>
                  while (ongoingProcesses.nonEmpty) {
                    val process = ongoingProcesses.remove(0)
                    if (process.isAlive) process.destroy()
                  }
                  Output.error(
                    s"Error with Perm ID= ${reserved.perm.id}: " + t.getMessage)
                  Left(t)
              }
              perfOption match {
                case Left(t) => reportError(reconstructedSourceText, reserved, t)
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
        DAO.reserveProgramForMeasurement(id, stressTable, config, conn)
    }
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

  class StressTable(workload: BenchmarkWorkload) {
    private val defaultStressValues = workload.stress match {
      case Some(value) => BenchmarkExternalConfig.generateStressList(value)
      case None => List.empty[Int]
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
      userConfiguredStressValues.getOrElse(filename, defaultStressValues)
    }
  }

}
