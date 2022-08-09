package gvc.benchmarking

import gvc.Config.error
import gvc.Main.resolveSilicon
import gvc.benchmarking.Benchmark.{
  BenchmarkException,
  injectStress,
  isInjectable
}
import gvc.benchmarking.BenchmarkPopulator.ProgramInformation
import gvc.benchmarking.DAO.{
  DBConnection,
  DynamicMeasurementMode,
  ErrorType,
  Identity,
  Permutation
}
import gvc.benchmarking.Timing.{CC0CompilationException, CC0ExecutionException}
import gvc.transformer.{IR, IRPrinter}
import gvc.weaver.WeaverException
import gvc.{Config, Main, VerificationException}
import viper.silicon.Silicon

import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.concurrent.TimeoutException

object BenchmarkExecutor {

  case class ReservedProgram(perm: Permutation,
                             workloads: List[Int],
                             measurementMode: Long)

  def execute(config: ExecutorConfig,
              baseConfig: Config,
              libraries: List[String]): Unit = {
    if (config.modifiers.onlyBenchmark) {
      Output.info("Targeting only benchmarks.")
    } else {
      Output.info("Targeting all available programs.")
    }
    val conn = DAO.connect(config.db)
    val id = DAO.addOrResolveIdentity(config, conn)
    var currentSiliconInstance: Option[Silicon] = None
    val ongoingProcesses = mutable.ListBuffer[scala.sys.process.Process]()
    val syncedPrograms = this.syncProgramsAndStress(id, config, libraries, conn)

    val tempBinary =
      Files.createTempFile("temp_bin", ".out")

    val tempSource =
      Files.createTempFile("temp_src", ".c0")

    var reservedProgram =
      DAO.reserveProgramForMeasurement(id, config.modifiers.onlyBenchmark, conn)

    def wrapTiming[T](f: => T): Either[Throwable, T] = {
      try {
        Right(
          Timeout.runWithTimeout(conn.gConfig.timeoutMinutes * 60 * 1000)(f))
      } catch {
        case t: Throwable =>
          while (ongoingProcesses.nonEmpty) {
            val process = ongoingProcesses.remove(0)
            if (process.isAlive) process.destroy()
          }
          currentSiliconInstance match {
            case Some(silicon) => silicon.stop()
            case None          =>
          }
          Output.error(t.getMessage)
          Left(t)
      }
    }

    def reportError(reserved: ReservedProgram, t: Throwable): Unit = {
      val typeToReport = t match {
        case _: VerificationException   => ErrorType.Verification
        case _: CC0CompilationException => ErrorType.Compilation
        case _: CC0ExecutionException   => ErrorType.Execution
        case _: TimeoutException        => ErrorType.Timeout
        case _: WeaverException         => ErrorType.Weaving
        case _                          => ErrorType.Unknown
      }
      DAO.logException(id, reserved, typeToReport, t.getMessage, conn)
    }

    def benchmarkGradual(ir: IR.Program,
                         reserved: ReservedProgram): Option[Path] = {
      val reconstructedSourceText =
        IRPrinter.print(ir, includeSpecs = true)

      currentSiliconInstance = Some(resolveSilicon(baseConfig))
      val vOut = wrapTiming(
        Timing.verifyTimed(currentSiliconInstance.get,
                           reconstructedSourceText,
                           Main.Defaults.outputFileCollection,
                           baseConfig))
      currentSiliconInstance = None

      vOut match {
        case Left(t) =>
          reportError(reserved, t)
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
      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${conn
          .dynamicModes(reserved.measurementMode)} | w=[${reserved.workloads
          .mkString(",")}] | id=${reserved.perm.id}")

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                              reserved.perm.permutationContents)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir).visit(asLabelSet)

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
              val perfOption = wrapTiming(
                Timing.execTimed(value,
                                 List(s"--stress $w"),
                                 config.workload.iterations,
                                 ongoingProcesses))
              perfOption match {
                case Left(t) => reportError(reserved, t)
                case Right(p) =>
                  DAO.completeProgramMeasurement(
                    id,
                    reserved,
                    w,
                    config.workload.staticIterations,
                    p,
                    conn)
              }
            })
        case None =>
      }
      reservedProgram = DAO.reserveProgramForMeasurement(
        id,
        config.modifiers.onlyBenchmark,
        conn)
    }
    DAO.cleanupStressValues(id, conn)
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
      case None =>
        workload.programCases.find(p => p.isDefault) match {
          case Some(value) =>
            BenchmarkExternalConfig.generateStressList(value.workload)
          case None => error("Unable to resolve default stress configuration.")
        }
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
  private def syncProgramsAndStress(
      id: Identity,
      config: ExecutorConfig,
      libraries: List[String],
      conn: DBConnection): Map[Long, ProgramInformation] = {
    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)
    val stressTable = new StressTable(config.workload)
    val translatedIDMapping = syncedPrograms.map(p => {
      val withoutExtension =
        p._2.fileName.substring(0, p._2.fileName.lastIndexOf(".c0"))
      p._1 -> stressTable.get(withoutExtension)
    })
    DAO.resolveStressValues(id, translatedIDMapping, conn)
    syncedPrograms
  }
}
