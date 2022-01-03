package gvc
import scala.language.postfixOps
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import java.nio.file.{Files, Paths}
import java.io.{File, FileWriter, IOException}
import java.util.regex.Pattern
import sys.process._

class CC0Options {
  var verbose: Boolean = false
  val libraries: mutable.ArrayBuffer[String] = ArrayBuffer()
  val includeDirs: mutable.ArrayBuffer[String] = ArrayBuffer()
  val programArgs: mutable.ArrayBuffer[String] = ArrayBuffer()
  val compilerArgs: mutable.ArrayBuffer[String] = ArrayBuffer()
  val warnings: mutable.ArrayBuffer[String] = ArrayBuffer()
  var dumpAST: Boolean = false
  var output: Option[String] = None
  var warn: Boolean = false
  var exec: Boolean = true
  var version: Boolean = false
  var logging: Boolean = true
  var dyn_checking: Boolean = false
  var compilerPath: Option[String] = None
  var use32BitArch: Boolean = false
  var saveIntermediateFiles: Boolean = false
  var genBytecode: Boolean = false
  var copy: Boolean = false
}

class CC0WrapperException(message: String) extends Exception(message)

object CC0Wrapper {
  val c0DependencyName = "runtime"
  val sourcePath = Paths
    .get(
      getClass.getResource("/" + c0DependencyName + ".c0").getPath
    )
    .toAbsolutePath
  val resourceDir = sourcePath.getRoot

  def exec(
      filename: String,
      program: String,
      options: CC0Options
  ): Int = {
    val verifiedFilename =
      if (options.copy) copyFile(filename, program) else filename
    val command: String = formatCommand(verifiedFilename, options)
    command !
  }

  def execCaptureOutput(
      filename: String,
      program: String,
      options: CC0Options
  ): String = {
    val verifiedFilename =
      if (options.copy) copyFile(filename, program) else filename
    val command: String = formatCommand(verifiedFilename, options)
    command !!
  }

  def copyFile(filename: String, program: String): String = {
    val verifiedFilename = "./" + filename + "_verified.c0"
    try {
      val fw = new FileWriter(new File(verifiedFilename))
      fw.write(program)
      fw.close()
    } catch {
      case ex: IOException =>
        throw new CC0WrapperException(
          "Unable to write verified file: " + ex.getMessage()
        )
    }
    verifiedFilename
  }

  private def formatCommand(filename: String, options: CC0Options): String = {
    var cmd = getCompilerPath(options.compilerPath) + filename
    if (options.exec) cmd += " -x"
    if (options.warn) cmd += " -w"
    if (options.verbose) cmd += " -v"
    if (!options.logging) cmd += " -n"
    if (options.genBytecode) cmd += " -b"
    if (options.saveIntermediateFiles) cmd += " -s"
    if (options.dumpAST) cmd += " --dump-ast"
    if (options.use32BitArch) cmd += " --bc-arch=32"

    for (elem <- options.warnings) {
      cmd += " -W" + elem
    }
    for (elem <- options.compilerArgs) {
      cmd += " -c " + elem
    }
    for (elem <- options.programArgs) {
      cmd += " -a " + elem
    }
    for (elem <- options.libraries) {
      cmd += " -l " + elem
    }
    for (elem <- options.includeDirs) {
      cmd += " -L " + elem
    }
    options.output match {
      case Some(value) => cmd += " -o " + value
      case None        =>
    }
    cmd
  }

  private def getCompilerPath(compilerPath: Option[String]): String = {
    compilerPath match {
      case Some(path) =>
        if (!Files.exists(Paths.get(path))) {
          throw new CC0WrapperException(
            "Unable to locate a cc0 executable at the path."
          )
        } else {
          path
        }
      case None => {
        val cc0 = System
          .getenv("PATH")
          .split(Pattern.quote(File.pathSeparator))
          .map((item) => Paths.get(item))
          .find((path) => Files.exists(path.resolve("cc0")))
        cc0 match {
          case Some(path) => path.toString
          case None =>
            throw new CC0WrapperException(
              "Unable to locate a cc0 executable in $PATH."
            )
        }
      }
    }
  }
}
