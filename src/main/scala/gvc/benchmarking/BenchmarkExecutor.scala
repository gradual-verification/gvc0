package gvc.benchmarking

import upickle.default._
import gvc.Config.error
import gvc.Main.resolveSilicon
import gvc.{Config, Main, VerificationException}
import gvc.benchmarking.Benchmark.injectAndWrite
import gvc.benchmarking.BenchmarkPopulator.md5sum
import gvc.benchmarking.BenchmarkRequest.{TaskRequest, TerminationRequest}
import gvc.benchmarking.BenchmarkResult.{DynamicResults, StaticFailure}
import gvc.benchmarking.DAO.{DynamicMeasurementMode, ErrorType}
import gvc.benchmarking.Timing.{CC0CompilationException, CC0ExecutionException}
import gvc.transformer.{IR, IRPrinter}
import gvc.transformer.IR.Program
import gvc.weaver.WeaverException
import upickle.default
import viper.silicon.Silicon

import sys.process.Process
import java.io.DataInputStream
import java.io.DataOutputStream
import java.net.{ConnectException, Socket}
import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.concurrent.TimeoutException

case class ExecutorSignature(version: String,
                             hardware: String,
                             nickname: String,
                             workloadsRequested: Map[String, List[Int]]) {
  override def toString: String =
    "(" + nickname + " | " + hardware + " | " + version.substring(
      0,
      Math.min(version.length, 6)) + ")"
}

object ExecutorSignature {
  implicit val rw: default.ReadWriter[ExecutorSignature] =
    macroRW[ExecutorSignature]
}

case class ProgramInformation(src: String,
                              ir: Program,
                              labels: LabelOutput,
                              fileName: String)

class BenchmarkExecutor(config: ExecutorConfig, baseConfig: Config) {

  private val tempBinary =
    Files.createTempFile("temp_bin", ".out")

  private val tempSource =
    Files.createTempFile("temp_src", ".c0")

  private var currentSiliconInstance: Option[Silicon] = None

  private var workRemaining = true;

  private val registeredPrograms =
    createProgramMapping(config.sources, Main.Defaults.includeDirectories)

  private val signature = write(
    ExecutorSignature(config.version,
                      config.hardware,
                      config.hardware,
                      createStressMapping(registeredPrograms, config.workload)))

  // initialize socket and input output streams
  def execute(): Unit = {
    try {
      val socket =
        new Socket(config.jobServerURL.getHost, config.jobServerURL.getPort)
      Output.success(s"Connection established to ${config.jobServerURL}")
      val input = new DataInputStream(socket.getInputStream)
      val output = new DataOutputStream(socket.getOutputStream)
      output.writeUTF(signature)
      Output.success(s"Awaiting job request...")
      while (workRemaining) {
        val request = read[BenchmarkRequest](input.readUTF())
        request match {
          case task: TaskRequest => {
            val result = benchmark(task)
            val serializedResult = write[BenchmarkResult](result)
            output.writeUTF(serializedResult)
          }
          case _: TerminationRequest =>
            Output.success(
              "Termination request received from job server; all work completed.")
            workRemaining = false
        }
      }
    } catch {
      case ce: ConnectException =>
        error(
          s"Unable to establish connection to ${config.jobServerURL}: ${ce.getMessage}")
    }
  }

  def benchmark(request: TaskRequest): BenchmarkResult = {
    val requestedProgram = this.registeredPrograms.get(request.md5) match {
      case Some(value) => value
      case None =>
        error("Received a request for a program that doesn't exist locally.")
    }
    Output.info(
      s"Benchmarking: ${requestedProgram.fileName} | ${request.mode} | ${request.workloads} | ID=${request.permutationID}")
    val astLabelSet =
      LabelTools.permutationIDToPermutation(requestedProgram.labels,
                                            request.permutation)
    val ir = new SelectVisitor(requestedProgram.ir)
      .visit(astLabelSet)
    val errorOccurred = request.mode match {
      case DynamicMeasurementMode.Dynamic | DynamicMeasurementMode.Framing =>
        benchmarkBaseline(ir, request.mode == DynamicMeasurementMode.Framing)
      case DynamicMeasurementMode.Gradual =>
        benchmarkGradual(ir)
    }
    (errorOccurred match {
      case Some(t) => StaticFailure(t)
      case None =>
        val resultMap = request.workloads
          .map(w => {
            w -> wrapTiming(30)(
              Timing.execTimed(tempBinary, List(s"--stress $w")))
          })
        val failures = resultMap
          .filter(pair => pair._2.isLeft)
          .map(p => p._1 -> p._2.left.get)
          .toMap
        val successes = resultMap
          .filter(pair => pair._2.isRight)
          .map(p => p._1 -> p._2.right.get)
          .toMap
        DynamicResults(failures, successes)
    }).asInstanceOf[BenchmarkResult]
  }

  def reportError(t: Throwable): BenchmarkError = {
    val typeToReport = t match {
      case _: VerificationException   => ErrorType.Verification
      case _: CC0CompilationException => ErrorType.Compilation
      case _: CC0ExecutionException   => ErrorType.Execution
      case _: TimeoutException        => ErrorType.Timeout
      case _: WeaverException         => ErrorType.Weaving
      case _                          => ErrorType.Unknown
    }
    BenchmarkError(t.getMessage, typeToReport)
  }

  def benchmarkBaseline(ir: IR.Program, onlyFraming: Boolean,
  ): Option[BenchmarkError] = {
    try {
      BaselineChecker.check(ir, onlyFraming)
      val sourceText =
        IRPrinter.print(ir, includeSpecs = false)
      injectAndWrite(sourceText, tempSource)
      Files.deleteIfExists(tempBinary)
      Timing.compileTimed(tempSource, tempBinary, baseConfig)
      None
    } catch {
      case t: Throwable => Some(reportError(t))
    }
  }

  def benchmarkGradual(ir: IR.Program): Option[BenchmarkError] = {
    val reconstructedSourceText =
      IRPrinter.print(ir, includeSpecs = true)
    currentSiliconInstance = Some(resolveSilicon(baseConfig))
    val vOut = wrapTiming(30)(
      Timing.verifyTimed(currentSiliconInstance.get,
                         reconstructedSourceText,
                         Main.Defaults.outputFileCollection,
                         baseConfig))
    currentSiliconInstance = None
    vOut match {
      case Left(t) =>
        Some(t)
      case Right(verified) =>
        injectAndWrite(verified.output.c0Source, tempSource)
        Files.deleteIfExists(tempBinary)
        Timing.compileTimed(tempSource, tempBinary, baseConfig)
        None
    }
  }

  def wrapTiming[T](timeoutMinutes: Int)(f: => T): Either[BenchmarkError, T] = {
    val ongoingProcesses = mutable.ListBuffer[Process]()
    try {
      Right(Timeout.runWithTimeout(timeoutMinutes * 60 * 1000)(f))
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
        Left(reportError(t))
    }
  }

  def createProgramMapping(
      sources: List[Path],
      libraries: List[String]): Map[String, ProgramInformation] = {
    sources
      .map(src => {
        val sourceText = Files.readString(src)
        val sourceIR = Main.generateIR(sourceText, libraries)
        val labelOutput = new LabelVisitor().visit(sourceIR)
        val fileName = src.getFileName.toString
        val programInfo =
          ProgramInformation(sourceText, sourceIR, labelOutput, fileName)
        val hash = md5sum(sourceText)
        hash -> programInfo
      })
      .toMap
  }

  def createStressMapping(
      programs: Map[String, ProgramInformation],
      workload: BenchmarkWorkload): Map[String, List[Int]] = {
    val programNamesToMD5 = programs.map(f => {
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
    val userConfiguredStressMappings = workload.programCases
      .flatMap(c => {
        val stressValues =
          BenchmarkExternalConfig.generateStressList(c.workload)
        for {
          i1: String <- c.matches
        } yield i1 -> stressValues
      })
      .toMap

    programNamesToMD5.map(p => {
      if (userConfiguredStressMappings.contains(p._1)) {
        p._2 -> userConfiguredStressMappings(p._1)
      } else {
        p._2 -> defaultStressValues
      }
    })
  }
}
