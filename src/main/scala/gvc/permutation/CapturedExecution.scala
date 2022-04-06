package gvc.permutation

import gvc.CC0Wrapper.{CommandOutput, Performance}
import gvc.{CC0Options, CC0Wrapper, Config}

import sys.process._
import java.io.ByteArrayOutputStream
import java.nio.file.{Path, Paths}
import scala.collection.mutable

object CapturedExecution {

  def compile(input: Path,
                    binary: Path,
                    config: Config
             ): CommandOutput = {
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(binary.toString),
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/"),
      compilerArgs = List()
    )
    val compileOutput = CC0Wrapper.exec_output(input.toString, cc0Options)
    if (compileOutput.exitCode != 0) {
      throw new CC0CompilationException(compileOutput)
    }else {
      compileOutput
    }
  }

  def compile_and_exec(input: Path, output: Path, iterations: Int, args: List[String], config: Config): Performance = {
    compile(input, output, config)
    exec_timed(output, iterations, args)
  }

  def exec_timed(
      binary: Path,
      iterations: Int,
      args: List[String]
  ): Performance = {
    var capture = ""
    val logger = ProcessLogger(
      (o: String) => capture += o,
      (e: String) => capture += e
    )
    val command = (List(binary.toAbsolutePath.toString) ++ args).mkString(" ")
    val timings = mutable.ListBuffer[Long]()
    var exitCode = 0
    for (_ <- 0 until iterations) {
      val start = System.nanoTime()
      exitCode = command ! logger

      val end = System.nanoTime()
      timings += end - start
      if (exitCode != 0) {
        throw new ExecutionException(CommandOutput(exitCode, capture))
      }
    }
    val med = median(timings.toList)
    val mean = timings.sum / timings.length
    val max = timings.max
    val min = timings.min
    val std = stdev(timings.toList, mean)
    new Performance(med, mean, std, min, max)
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

  class CapturedOutputException(output: CommandOutput)
      extends Exception {
    def logMessage(name: String, printer: ErrorCSVPrinter): Unit = {
      printer.log(name, output.exitCode, output.output)
    }
  }
  class CC0CompilationException(output: CommandOutput)
      extends CapturedOutputException(output)

  class ExecutionException(output: CommandOutput)
      extends CapturedOutputException(output)
}
