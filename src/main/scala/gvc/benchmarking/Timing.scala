package gvc.benchmarking

import gvc.{CC0Options, CC0Wrapper, Config, OutputFileCollection}
import gvc.CC0Wrapper.{CommandOutput, Performance}
import gvc.Main.{VerifiedOutput, verify}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.concurrent.duration._
import scala.language.postfixOps
import java.math.MathContext
import java.nio.file.Path
import java.nio.file.Paths
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import sys.process._

object Timing {

  case class TimedVerification(
      output: VerifiedOutput,
      translation: Performance,
      verification: Performance,
      instrumentation: Performance
  )

  def verifyTimed(
      inputSource: String,
      fileNames: OutputFileCollection,
      config: Config,
  ): TimedVerification = {
    var verifiedOutput: Option[VerifiedOutput] = None
    val translationTimings = ListBuffer[Long]()
    val verifierTimings = ListBuffer[Long]()
    val weaverTimings = ListBuffer[Long]()

    for (_ <- 0 until 1) {
      val out = verify(inputSource, fileNames, config)
      val perf = out.timing
      translationTimings += perf.translation
      verifierTimings += perf.verification
      weaverTimings += perf.instrumentation
      verifiedOutput = Some(out)
    }
    val perfTranslation = generatePerformanceStats(translationTimings.toList)
    val perfVerification = generatePerformanceStats(verifierTimings.toList)
    val perfInstrumentation = generatePerformanceStats(weaverTimings.toList)
    TimedVerification(
      verifiedOutput.get,
      perfTranslation,
      perfVerification,
      perfInstrumentation
    )
  }

  def compileTimed(
      input: Path,
      binary: Path,
      config: Config,
      iterations: Int
  ): Performance = {
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(binary.toString),
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/")
    )
    if (System.getProperty("mrj.version") != null) {
      // the upper bound on nested brackets is lower for clang than for gcc, leading to compilation failures.
      // cc0 is hardcoded to use gcc, but "gcc" is an alias for clang in mac os
      cc0Options.compilerArgs = List("-fbracket-depth=1024")
    }

    val compilationCommand = CC0Wrapper
      .formatCommand(input.toAbsolutePath.toString, cc0Options)
      .mkString(" ")
    def compileOnError(output: CommandOutput): Unit = {
      throw new CC0CompilationException(output)
    }
    runTimedCommand(
      iterations,
      compilationCommand,
      compileOnError
    )
  }

  def compileAndExec(
      input: Path,
      output: Path,
      args: List[String],
      config: Config,
      benchConfig: SequentialConfig
  ): (Performance, Performance) = {
    (
      compileTimed(input, output, config, benchConfig.workload.iterations),
      execTimed(output, benchConfig.workload.iterations, args)
    )
  }

  private def runTimedCommand(
      iterations: Int,
      command: String,
      onNonzero: (CommandOutput) => Unit
  ): Performance = {
    var capture = ""
    val logger = ProcessLogger(
      (o: String) => capture += o,
      (e: String) => capture += e
    )

    val timings = mutable.ListBuffer[Long]()
    for (_ <- 0 until iterations) {
      val start = System.nanoTime()
      val result = command ! logger
      val end = System.nanoTime()
      if (result != 0) {
        onNonzero(CommandOutput(result, capture))
      }
      timings += end - start
    }
    generatePerformanceStats(timings.toList)
  }

  def generatePerformanceStats(timings: List[Long]): Performance = {
    val ninety_fifth = percentile(timings, .95)
    val fifth = percentile(timings, .5)
    val med = median(timings)
    val sum = BigDecimal(timings.sum)
    val mean = sum / timings.length

    val max = timings.max
    val min = timings.min
    val std = stdev(timings, mean)
    new Performance(ninety_fifth, fifth, med, mean, std, min, max)
  }

  def execTimed(
      binary: Path,
      iterations: Int,
      args: List[String]
  ): Performance = {
    val command = (List(binary.toAbsolutePath.toString) ++ args).mkString(" ")
    def execNonzero(output: CommandOutput): Unit = {
      throw new ExecutionException(output)
    }
    runTimedCommand(iterations, command, execNonzero)
  }

  private def percentile(values: List[Long], percentile: Double): BigDecimal = {
    val proportion = BigDecimal(percentile) * (values.size - 1)
    if (proportion < 1)
      values.head
    else if (proportion >= values.size)
      values.last
    else {
      val fractional = proportion - proportion.toBigInt().toInt
      val sorted_list = values.sortWith((a, b) => {
        a < b
      })
      val base = sorted_list(proportion.toBigInt().toInt)
      val max = sorted_list(proportion.toBigInt().toInt + 1)
      val diff = (max - base) * fractional
      base + diff
    }
  }

  private def median(values: List[Long]): BigDecimal = {
    val lst = values.sorted
    if (lst.length % 2 == 0) {
      val l = lst(lst.length / 2)
      val r = lst(lst.length / 2 - 1)
      val max = BigDecimal(l + r)
      max / 2
    } else {
      lst(lst.length / 2)
    }
  }

  private def stdev(values: List[Long], mean: BigDecimal): BigDecimal = {
    if (values.length > 1) {
      val collected =
        values.map(v => v - mean).map(m => m * m).sum / (values.length - 1)
      val square_rooted = BigDecimal(
        collected.underlying().sqrt(MathContext.DECIMAL128)
      )
      square_rooted.setScale(2, BigDecimal.RoundingMode.HALF_EVEN)
    } else 0
  }

  class CapturedOutputException(output: CommandOutput) extends Exception {
    def logMessage(name: String, printer: ErrorCSVPrinter): Unit = {
      printer.log(name, output.exitCode, output.output)
    }
  }
  class CC0CompilationException(output: CommandOutput)
      extends CapturedOutputException(output)

  class ExecutionException(output: CommandOutput)
      extends CapturedOutputException(output)
}

object Timeout {
  def runWithTimeout[T](timeoutMs: Long)(f: => T): Option[T] = {
    Some(Await.result(Future(f), timeoutMs milliseconds))
  }

  def formatMilliseconds(ms: Long): String = {
    if (ms > 1000 * 60 * 60) {
      s"${(ms / (1000 * 60 * 60))} hr"
    } else if (ms > 1000 * 60) {
      s"${(ms / (1000 * 60))} min"
    } else if (ms > 1000) {
      s"${ms / 1000} sec"
    } else {
      s"$ms ms"
    }
  }
}
