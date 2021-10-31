package gvc.verifier

import gvc.parser._
import org.scalatest.funsuite._
import java.io.File
import scala.io.Source
import fastparse.Parsed.Success
import gvc.analyzer.{Resolver, ErrorSink, TypeChecker, AssignmentValidator}
import gvc.analyzer.ReturnValidator
import gvc.transformer.Transformer
import gvc.transformer.SilverOutput
import gvc.analyzer.SpecificationValidator
import gvc.analyzer.ImplementationValidator
import gvc.weaver.Weaver
import viper.silicon.Silicon
import viper.silver.verifier.Failure
import org.scalatest.BeforeAndAfterAll
import gvc.transformer.CNaughtPrinter

class VerifierSpecs extends AnyFunSuite with BeforeAndAfterAll {
  var silicon: Silicon = null

  val testDir = "verifier/"
  val testFiles = (new File(getClass().getResource("/" + testDir).getFile()).listFiles())
      .map { file => (testDir + file.getName().toLowerCase(), file) }
      .filter { case (name, _) => name.endsWith(".c0") && !name.endsWith(".output.c0") }

  for ((name, file) <- testFiles) {
    test("test " + name) {
      val dir = file.getParentFile()
      val silverFile = new File(dir, file.getName().replace(".c0", ".vpr"))
      val outputFile = new File(dir, file.getName().replace(".c0", ".output.c0"))

      val src = Source.fromFile(file).mkString
      val expectedSilver = Source.fromFile(silverFile).mkString
      val expectedOutput = Source.fromFile(outputFile).mkString
      runVerifierTest(src, expectedSilver, expectedOutput)
    }
  }

  def runVerifierTest(source: String, expectedSilver: String, expectedOutput: String) = {
    val Success(parsed, _) = Parser.parseProgram(source)
    val sink = new ErrorSink()

    val result = Resolver.resolveProgram(parsed, sink)
    assert(sink.errors.isEmpty)

    TypeChecker.check(result, sink)
    assert(sink.errors.isEmpty)

    AssignmentValidator.validate(result, sink)
    ReturnValidator.validate(result, sink)
    SpecificationValidator.validate(result, sink)
    ImplementationValidator.validate(result, sink)
    assert(sink.errors.isEmpty)

    var ir = Transformer.programToIR(result)
    val silver = SilverOutput.program(ir)
    
    assert(silver.toString == expectedSilver)

    silicon.verify(silver) match {
      case viper.silver.verifier.Success => ()
      case Failure(errors) => fail(errors.map(e => e.toString()).mkString("\n"))
    }

    val program = Weaver.weave(ir, silver)
    assert(CNaughtPrinter.printProgram(program) == expectedOutput)
  }

  override protected def beforeAll(): Unit = {
    val z3 = sys.env.get("Z3_EXE")
    assert(z3.isDefined, "Configure the Z3_EXE variable with the full path to Z3")

    val reporter = viper.silver.reporter.NoopReporter
    silicon = Silicon.fromPartialCommandLineArguments(Seq("--z3Exe", z3.get), reporter, Seq())
    silicon.start()
  }

  override protected def afterAll(): Unit = {
    silicon.stop()
    silicon = null
  }
}

