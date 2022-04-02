package gvc.permutation

import gvc.CC0Wrapper.{CompilationOutput, ExecutionOutput, Performance}
import gvc.{CC0Options, CC0Wrapper, Config}
import sys.process._
import java.io.ByteArrayOutputStream
import java.nio.file.{Path, Paths}
import scala.collection.mutable

object CapturedExecution {

  def compile_and_exec(
      input: Path,
      binary: Path,
      iterations: Int,
      config: Config
  ): Performance = {
    val output = compile(
      input,
      binary,
      config
    )
    if (output.exitCode != 0) {
      throw new CC0CompilationException(output)
    } else {
      val exec = exec_timed(binary, iterations)
      exec.perf match {
        case Some(value) => value
        case None        => throw new ExecutionException(exec)
      }
    }
  }
  def compile(
      input: Path,
      output: Path,
      config: Config
  ): CompilationOutput = {
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(output.toString),
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/"),
      compilerArgs = List("-fbracket-depth=1024")
    )
    CC0Wrapper.exec_output(input.toString, cc0Options)
  }
  def exec_timed(
      binary: Path,
      iterations: Int
  ): ExecutionOutput = {
    var capture = ""
    val logger = ProcessLogger(
      (o: String) => capture += o,
      (e: String) => capture += e
    )
    val command = binary.toAbsolutePath.toString
    val timings = mutable.ListBuffer[Long]()
    val os = new ByteArrayOutputStream()
    var exitCode = 0
    for (_ <- 0 until iterations) {
      val start = System.nanoTime()
      exitCode = (command ! logger)

      val end = System.nanoTime()
      timings += end - start
      if (exitCode != 0) {
        return ExecutionOutput(
          exitCode,
          capture,
          None
        )
      } else {
        os.reset()
      }
    }
    val med = median(timings.toList)
    val mean = timings.sum / timings.length
    val max = timings.max
    val min = timings.min
    val std = stdev(timings.toList, mean)

    ExecutionOutput(
      exitCode,
      os.toString("UTF-8"),
      Some(new Performance(med, mean, std, min, max))
    )
  }

  def median(values: List[Long]): Long = {
    val lst = values.sorted
    if (lst.length % 2 == 0) {
      val l = lst(lst.length / 2)
      val r = lst(lst.length / 2 - 1)
      (l + r) / 2
    } else {
      lst(lst.length / 2)
    }
  }

  def stdev(values: List[Long], mean: Long): Long = {
    if (values.length > 1)
      Math
        .sqrt(
          values.map(_ - mean).map(m => m * m).sum / (values.length - 1)
        )
        .toLong
    else 0
  }

  class CapturedOutputException(exitCode: Int, stdout: String)
      extends Exception {
    def logMessage(name: String, printer: ErrorCSVPrinter): Unit = {
      printer.log(name, exitCode, stdout)
    }
  }
  class CC0CompilationException(output: CompilationOutput)
      extends CapturedOutputException(output.exitCode, output.output)
  class ExecutionException(output: ExecutionOutput)
      extends CapturedOutputException(output.exitCode, output.output)
}
