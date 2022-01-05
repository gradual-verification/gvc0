package gvc

import gvc.parser.Parser
import fastparse.Parsed.{Failure, Success}
import gvc.analyzer._
import gvc.transformer._
import gvc.weaver.Weaver
import viper.silicon.Silicon
import viper.silver.verifier
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import java.io.IOException
import sys.process._
import scala.language.postfixOps

object Main extends App {
  val cmdConfig = Config.fromCommandLineArgs(args.toList)
  cmdConfig.validate()
  run(cmdConfig)

  def run(config: Config): Unit = {
    val sourceFile = config.sourceFile.get

    val baseName =
      if (sourceFile.toLowerCase().endsWith(".c0"))
        sourceFile.slice(0, sourceFile.length() - 3)
      else sourceFile
    var irFileName = baseName + ".ir.c0"
    val silverFileName = baseName + ".vpr"
    val c0FileName = baseName + ".verified.c0"

    val inputSource = readFile(config.sourceFile.get)

    val parsed = Parser.parseProgram(inputSource) match {
      case fail: Failure =>
        Config.error(s"Parse error:\n${fail.trace().longAggregateMsg}")
      case Success(value, index) => value
    }

    val errors = new ErrorSink()
    val resolved = Validator
      .validateParsed(parsed, errors)
      .getOrElse(
        Config.error(
          s"Errors:\n" +
            errors.errors.map(_.toString()).mkString("\n")
        )
      )

    val ir = GraphTransformer.transform(resolved)
    if (config.dump == Some(Config.DumpIR)) dump(GraphPrinter.print(ir))
    else if (config.saveFiles) writeFile(irFileName, GraphPrinter.print(ir))

    val silver = IRGraphSilver.toSilver(ir)
    if (config.dump == Some(Config.DumpSilver)) dump(silver.toString())
    else if (config.saveFiles) writeFile(silverFileName, silver.toString())

    val reporter = viper.silver.reporter.StdIOReporter()
    val z3Exe = Config.resolveToolPath("z3", "Z3_EXE")
    val silicon = Silicon.fromPartialCommandLineArguments(
      Seq("--z3Exe", z3Exe),
      reporter,
      Seq()
    )

    silicon.start()

    silicon.verify(silver) match {
      case verifier.Success => ()
      case verifier.Failure(errors) => {
        Config.error(
          s"Verification errors:\n" +
            errors.map(_.readableMessage).mkString("\n")
        )
      }
    }

    if (config.onlyVerify) sys.exit(0)

    Weaver.weave(ir, silver)

    silicon.stop()

    val c0Source = GraphPrinter.print(ir)
    if (config.dump == Some(Config.DumpC0)) dumpC0(c0Source)

    val outputExe = config.output.getOrElse("a.out")
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(outputExe)
    )

    // Always write the intermediate C0 file, but then delete it
    // if not saving intermediate files
    writeFile(c0FileName, c0Source)
    val compilerExit =
      try {
        CC0Wrapper.exec(c0FileName, cc0Options)
      } finally {
        if (!config.saveFiles) deleteFile(c0FileName)
      }

    if (compilerExit != 0) Config.error("Compilation failed")

    if (config.exec) {
      val outputCommand = Paths.get(outputExe).toAbsolutePath().toString()
      sys.exit(Seq(outputCommand) !)
    } else {
      sys.exit(0)
    }
  }

  def readFile(file: String): String =
    try {
      Files.readString(Paths.get(file))
    } catch {
      case _: IOException => Config.error(s"Could not read file 'file'")
    }

  def writeFile(file: String, contents: String): Unit =
    try {
      Files.writeString(Paths.get(file), contents, StandardCharsets.UTF_8)
    } catch {
      case _: IOException => Config.error(s"Could not write file 'file'")
    }

  def deleteFile(file: String): Unit =
    try {
      Files.delete(Paths.get(file))
    } catch {
      case _: IOException => Config.error(s"Could not delete file 'file'")
    }

  def dump(output: String): Nothing = {
    println(output)
    sys.exit(0)
  }

  def dumpC0(output: String): Nothing = {
    // Print runtime check information for debugging when dumping C0 output
    // This only happens after verification, so runtime checks have been initialized
    for ((exp, checks) <- viper.silicon.state.runtimeChecks.getChecks) {
      println("Runtime checks required for " + exp.toString() + ":")
      println(
        checks
          .map(b =>
            "  if " + (if (b.branch.branch.isEmpty) "true"
                       else
                         b.branch.branch
                           .map(c => "(" + c.toString() + ")")
                           .mkString(" && ")) + ": " +
              b.checks.toString()
          )
          .mkString("\n")
      )
    }

    dump(output)
  }
}
