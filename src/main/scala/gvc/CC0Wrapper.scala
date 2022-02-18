package gvc

import sys.process._
import scala.language.postfixOps

sealed trait CC0Architecture { val name: String }
object CC0Architecture {
  case object Arch32 { val name = "32" }
  case object Arch64 { val name = "64" }
}

case class CC0Options(
    compilerPath: String = "cc0",
    verbose: Boolean = false,
    libraries: List[String] = Nil,
    includeDirs: List[String] = Nil,
    execArgs: List[String] = Nil,
    compilerArgs: List[String] = Nil,
    warnings: List[String] = Nil,
    dumpAST: Boolean = false,
    output: Option[String] = None,
    warn: Boolean = false,
    exec: Boolean = false,
    version: Boolean = false,
    log: Boolean = true,
    dynCheck: Boolean = false,
    purityCheck: Boolean = true,
    saveIntermediateFiles: Boolean = false,
    genBytecode: Boolean = false,
    copy: Boolean = false,
    standard: Option[String] = None,
    runtime: Option[String] = None,
    architecture: Option[CC0Architecture] = None,
    onlyTypecheck: Boolean = false,
    includeRuntime: Boolean = false,
    inputFiles: List[String] = Nil
)

case class ExecutionMetrics(
    real: Long,
    user: Long,
    sys: Long
)

object CC0Wrapper {
  private val real = {
    "([0-9]+\\.[0-9]+) real".r
  }
  private val user = {
    "([0-9]+\\.[0-9]+) user".r
  }
  private val sys = {
    "([0-9]+\\.[0-9]+) sys".r
  }

  class CC0Exception(val message: String) extends RuntimeException {
    override def getMessage(): String = message
  }

  def exec(sourceFile: String, options: CC0Options): Int = {
    val command = formatCommand(sourceFile, options)
    command !
  }

  def execTimed(sourceFile: String, options: CC0Options): ExecutionMetrics = {
    val command = formatCommand(sourceFile, options)
    val timedCommand = "/usr/bin/time -p " + command
    val results = timedCommand !!

    val outputLines = results.split("\n")

    if (outputLines.length < 3) {
      throw new CC0Exception(
        "Unable to extract timing information from stdout."
      )
    } else {
      val realMatch = real.findFirstIn(outputLines(outputLines.length - 2))
      val userMatch = user.findFirstIn(outputLines(outputLines.length - 1))
      val sysMatch = sys.findFirstIn(outputLines.last)

      if (realMatch.isDefined && userMatch.isDefined && sysMatch.isDefined) {
        ExecutionMetrics(
          realMatch.get.toLong,
          userMatch.get.toLong,
          sysMatch.get.toLong
        )
      } else {
        throw new CC0Exception(
          "Unable to extract timing information from stdout."
        )
      }
    }
  }

  private def formatCommand(
      sourceFile: String,
      options: CC0Options
  ): List[String] = {
    def flag(arg: String, flag: Boolean): Seq[String] =
      if (flag) Seq(arg) else Seq.empty
    def values(arg: String, values: Seq[String]): Seq[String] =
      values.flatMap(value =>
        if (arg.startsWith("--")) Seq(s"$arg=$value") else Seq(arg, value)
      )
    def value(arg: String, value: Option[String]): Seq[String] =
      values(arg, value.toSeq)

    Seq(
      Seq(options.compilerPath),
      flag("--verbose", options.verbose),
      flag("--dyn-check", options.dynCheck),
      flag("--no-purity-check", !options.purityCheck),
      values("--library", options.libraries),
      values("-L", options.includeDirs),
      values("-a", options.execArgs),
      value("--standard", options.standard),
      flag("--no-log", !options.log),
      flag("--dump-ast", options.dumpAST),
      flag("--save-files", options.saveIntermediateFiles),
      value("--runtime", options.runtime),
      flag("--bytecode", options.genBytecode),
      value("--bc-arch", options.architecture.map(_.name)),
      value("--output", options.output),
      values("-c", options.compilerArgs),
      flag("--warn", options.warn),
      flag("--exec", options.exec),
      flag("--only-typecheck", options.onlyTypecheck),
      options.inputFiles.flatMap(value => Seq(value)),
      Seq(sourceFile)
    ).flatten.toList
  }
}
