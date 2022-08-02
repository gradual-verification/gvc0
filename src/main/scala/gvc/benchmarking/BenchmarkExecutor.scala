package gvc.benchmarking

import gvc.Config.error
import gvc.Main.resolveSilicon
import gvc.benchmarking.Benchmark.{
  BenchmarkException,
  injectStress,
  isInjectable
}
import gvc.benchmarking.BenchmarkPopulator.ProgramInformation
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType, Permutation}
import gvc.benchmarking.Timing.{
  CC0CompilationException,
  CC0ExecutionException,
  execTimed
}
import gvc.transformer.{IR, IRPrinter}
import gvc.weaver.WeaverException
import gvc.{Config, Main, VerificationException}
import viper.silicon.Silicon

import java.nio.file.{Files, Path}
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
                             workloads: List[Int],
                             measurementMode: Long)

  def execute(config: ExecutorConfig,
              baseConfig: Config,
              libraries: List[String]): Unit = {

    val conn = DAO.connect(config.db)
    val globalConfig = DAO.resolveGlobalConfiguration(conn)
    val id = DAO.addOrResolveIdentity(config, conn)
    val modes = DAO.resolveDynamicModes(conn)
    var currentSiliconInstance: Option[Silicon] = None

    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)

    val stressEntries =
      this.createTemporaryStressEntries(syncedPrograms, config.workload)

    val workload = config.workload

    val tempBinary =
      Files.createTempFile("temp_bin", ".out")

    val tempSource =
      Files.createTempFile("temp_src", ".c0")

    var reservedProgram =
      DAO.reserveProgramForMeasurement(id, stressEntries, conn)

    def wrapTiming(binary: Path, reserved: ReservedProgram, workload: Int,
    ): Unit = {
      val timingStart = System.nanoTime()
      try {
        val perf =
          Timeout.runWithTimeout(globalConfig.timeoutMinutes * 60 * 1000)(
            execTimed(binary,
                      config.workload.iterations,
                      List(s"--stress $workload")))

        DAO.completeProgramMeasurement(id,
                                       reserved,
                                       workload,
                                       config.workload.iterations,
                                       perf,
                                       conn)
      } catch {
        case t: Throwable =>
          val timingStop = System.nanoTime()
          val differenceSeconds: Long =
            Math.floor((timingStop - timingStart) * Math.pow(10, 9)).toLong
          currentSiliconInstance match {
            case Some(silicon) => silicon.stop()
            case None          =>
          }
          val errorType = t match {
            case _: TimeoutException        => ErrorType.Timeout
            case _: VerificationException   => ErrorType.Verification
            case _: CC0CompilationException => ErrorType.Compilation
            case _: CC0ExecutionException   => ErrorType.Execution
            case _: WeaverException         => ErrorType.Weaving
            case _                          => ErrorType.Unknown
          }
          Output.error(t.getMessage)
          DAO.logException(id,
                           reserved,
                           errorType,
                           t.getMessage,
                           differenceSeconds,
                           conn)
      }
    }

    def benchmarkGradual(ir: IR.Program, reserved: ReservedProgram): Unit = {
      currentSiliconInstance = Some(resolveSilicon(baseConfig))
      val reconstructedSourceText =
        IRPrinter.print(ir, includeSpecs = true)

      val vOut = Timing.verifyTimed(currentSiliconInstance.get,
                                    reconstructedSourceText,
                                    Main.Defaults.outputFileCollection,
                                    baseConfig,
                                    workload.staticIterations)
      currentSiliconInstance = None

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
    }

    def benchmarkBaseline(ir: IR.Program, onlyFraming: Boolean): Unit = {
      BaselineChecker.check(ir, onlyFraming)
      val sourceText =
        IRPrinter.print(ir, includeSpecs = false)
      this.injectAndWrite(sourceText, tempSource)
      Files.deleteIfExists(tempBinary)
      Timing.compileTimed(tempSource,
                          tempBinary,
                          baseConfig,
                          workload.staticIterations)
    }

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      Output.info(
        s"Benchmarking: ${syncedPrograms(reserved.perm.programID).fileName} | ${modes(
          reserved.measurementMode)} | w=[${reserved.workloads
          .mkString(",")}] | id=${reserved.perm.id}")

      val correspondingProgramLabels =
        syncedPrograms(reserved.perm.programID).labels

      val asLabelSet =
        LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                              reserved.perm.permutationHash)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).ir).visit(asLabelSet)

      modes.get(reserved.measurementMode) match {
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
      reserved.workloads
        .foreach(w => {
          wrapTiming(tempBinary, reserved, w)
        })
      reservedProgram =
        DAO.reserveProgramForMeasurement(id, stressEntries, conn)
    }
  }

  case class WorkloadEntry(programID: Long, workloadValue: Int)

  def createTemporaryStressEntries(
      programs: Map[Long, ProgramInformation],
      workload: BenchmarkWorkload): List[WorkloadEntry] = {

    val programNamesToIDs = programs.map(f => {
      val withoutExtention =
        f._2.fileName.substring(0, f._2.fileName.lastIndexOf('.'))
      withoutExtention -> f._1
    })

    val defaultStressValues = workload.stress match {
      case Some(value) => BenchmarkExternalConfig.generateStressList(value)
      case None =>
        workload.programCases.find(p => p.isDefault) match {
          case Some(value) =>
            BenchmarkExternalConfig.generateStressList(value.workload)
          case None => error("Unable to resolve default stress configuration.")
        }
    }
    val unspecifiedButExistingPrograms = programNamesToIDs.keySet
      .filter(k => !workload.programCases.exists(cs => cs.matches.contains(k)))
      .map(programNamesToIDs(_))

    val defaultStressMappings = (for {
      i1: Long <- unspecifiedButExistingPrograms
      i2: Int <- defaultStressValues
    } yield WorkloadEntry(i1, i2)).toList

    val userConfiguredStressMappings = workload.programCases
      .flatMap(c => {
        val stressValues =
          BenchmarkExternalConfig.generateStressList(c.workload)
        for {
          i1: Long <- c.matches
            .filter(programNamesToIDs.contains)
            .map(programNamesToIDs)
          i2: Int <- stressValues
        } yield WorkloadEntry(i1, i2)
      })
    defaultStressMappings ++ userConfiguredStressMappings
  }
}
