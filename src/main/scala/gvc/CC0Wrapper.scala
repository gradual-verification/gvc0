package gvc

import gvc.Main.getClass

import java.io.File
import sys.process._
import scala.language.postfixOps

sealed trait CC0Architecture { val name: String }
object CC0Architecture {
  case object Arch32 { val name = "32" }
  case object Arch64 { val name = "64" }
}

case class CC0Options(
  val compilerPath: String = "cc0",
  val verbose: Boolean = false,
  val libraries: List[String] = Nil,
  val includeDirs: List[String] = Nil,
  val execArgs: List[String] = Nil,
  val compilerArgs: List[String] = Nil,
  val warnings: List[String] = Nil,
  val dumpAST: Boolean = false,
  val output: Option[String] = None,
  val warn: Boolean = false,
  val exec: Boolean = false,
  val version: Boolean = false,
  val log: Boolean = true,
  val dynCheck: Boolean = false,
  val purityCheck: Boolean = true,
  val saveIntermediateFiles: Boolean = false,
  val genBytecode: Boolean = false,
  val copy: Boolean = false,
  val standard: Option[String] = None,
  val runtime: Option[String] = None,
  val architecture: Option[CC0Architecture] = None,
  val onlyTypecheck: Boolean = false,
  val includeRuntime: Boolean = false,
  val inputFiles: List[String] = Nil,
)

object CC0Wrapper {
  def exec(sourceFile: String, options: CC0Options): Int = {
    val command = formatCommand(sourceFile, options)
    command !
  }

  private def formatCommand(sourceFile: String, options: CC0Options): List[String] = {
    def flag(arg: String, flag: Boolean): Seq[String] =
      if (flag) Seq(arg) else Seq.empty
    def values(arg: String, values: Seq[String]): Seq[String] =
      values.flatMap(value => if (arg.startsWith("--")) Seq(s"$arg=$value") else Seq(arg, value))
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
