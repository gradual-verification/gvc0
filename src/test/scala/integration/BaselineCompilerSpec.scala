package gvc.specs.integration

import org.scalatest.funsuite.AnyFunSuite
import java.lang.ProcessBuilder.Redirect

import gvc.specs._
import org.scalatest._
import java.nio.file._
import gvc.specs.BaseFileSpec
import scala.io.Source
import gvc.parser.Parser
import fastparse.Parsed.{Failure, Success}
import gvc.analyzer.{ErrorSink, Validator}
import gvc.transformer.{IRTransformer, IRPrinter}
import gvc.benchmarking.BaselineChecks

class BaselineCompilerSpec extends AnyFunSuite with BaseFileSpec with ParallelTestExecution {
  var output: Path = null
  val includeDirs = gvc.Main.Defaults.includeDirectories

  override protected def withFixture(test: NoArgTest): Outcome = {
    try {
      output = Files.createTempDirectory("gvc0")
      super.withFixture(test)
    } finally {
      TestUtils.deleteDirectory(output)
    }
  }

  def compile(args: String*): Unit =
    execute(("cc0" :: includeDirs.flatMap(dir => List("-L", dir)) ::: args.toList):_*)

  def execute(command: String*): Unit = {
    val proc = new ProcessBuilder(command:_*)
      .redirectError(Redirect.INHERIT)
      .redirectOutput(Redirect.PIPE)
      .start()

    val exit = proc.waitFor()
    if (exit != 0) {
      info("Output: " + Source.fromInputStream(proc.getInputStream()).mkString)
      fail(s"Command '${command.mkString(" ")}' exited with code $exit")
    }
  }

  val inputFiles =
    TestUtils.groupResources("verifier") ++
    TestUtils.groupResources("quant-study") ++
    TestUtils.groupResources("baseline")

  inputFiles.foreach { input =>
    test(s"baseline compile and run ${input.name}") {
      val source = input(".c0").read()
      val id = input.id

      val parsed = Parser.parseProgram(source) match {
        case err: Failure =>
          fail(s"Parse error:\n${err.trace().longAggregateMsg}")
        case Success(value, _) => value
      }
      val errors = new ErrorSink()
      val resolved = Validator
        .validateParsed(parsed, includeDirs, errors)
        .getOrElse(
          fail(errors.errors.map(_.toString()).mkString("\n"))
        )
      val program = IRTransformer.transform(resolved)

      BaselineChecks.insert(program)
      
      val baselineSource = IRPrinter.print(program, false)
      val baselineFile = output.resolve(id + ".baseline.c0")
      Files.writeString(baselineFile, baselineSource)

      assertFile(input.get(".baseline.c0"), baselineSource)

      val outputExe = output.resolve(id)
      compile(s"--output=${outputExe}", baselineFile.toString())

      execute(outputExe.toString())
    }
  }
}