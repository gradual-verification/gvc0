package gvc.permutation

import gvc.CC0Wrapper.{CompilationOutput, ExecutionOutput, Performance}
import gvc.{CC0Options, CC0Wrapper, Config}
import sys.process._
import scala.language.postfixOps
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
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/")
    )
    CC0Wrapper.exec_output(input.toString, cc0Options)
  }
  def exec_timed(
      binary: Path,
      iterations: Int
  ): ExecutionOutput = {
    val command = binary.toAbsolutePath.toString + " 2>&1"
    val timings = mutable.ListBuffer[Long]()
    val os = new ByteArrayOutputStream()
    var exitCode = 0
    for (_ <- 0 until iterations) {
      val start = System.nanoTime()
      exitCode = (command #> os) !

      val end = System.nanoTime()
      timings += end - start
      if (exitCode != 0) {
        return ExecutionOutput(
          exitCode,
          os.toString("UTF-8"),
          None
        )
      } else {
        os.reset()
      }
    }
    val mean = timings.sum / timings.length
    val max = timings.max
    val min = timings.min
    val stdev =
      if (timings.length > 1)
        Math.sqrt(
          timings.map(_ - mean).map(m => m * m).sum / (timings.length - 1)
        )
      else 0
    ExecutionOutput(
      exitCode,
      os.toString("UTF-8"),
      Some(new Performance(mean, stdev, min, max))
    )
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
