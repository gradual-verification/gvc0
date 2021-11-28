package gvc.verifier

import fastparse.Parsed.Success
import gvc.analyzer.ErrorSink
import gvc.analyzer.Validator
import gvc.parser._
import gvc.transformer.GraphPrinter
import gvc.transformer.GraphTransformer
import gvc.transformer.IRGraphSilver
import gvc.weaver.Weaver
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite._
import viper.silicon.Silicon
import viper.silver.verifier.Failure

import java.io.File
import scala.io.Source

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

    val result = Validator.validateParsed(parsed, sink)
    assert(sink.errors.isEmpty)
    assert(result.isDefined)

    var ir = GraphTransformer.transform(result.get)
    val silver = IRGraphSilver.toSilver(ir)
    
    assert(silver.toString == expectedSilver)

    silicon.verify(silver) match {
      case viper.silver.verifier.Success => ()
      case Failure(errors) => fail(errors.map(e => e.toString()).mkString("\n"))
    }

    Weaver.weave(ir, silver)
    assert(GraphPrinter.print(ir) == expectedOutput)
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

