package gvc.verifier

import fastparse.Parsed.Success
import gvc.Config
import gvc.analyzer.ErrorSink
import gvc.analyzer.Validator
import gvc.parser._
import gvc.transformer.GraphPrinter
import gvc.transformer.GraphTransformer
import gvc.transformer.IRGraphSilver
import gvc.weaver.Weaver
import org.scalatest.funsuite._
import viper.silicon.Silicon
import viper.silver.verifier.Failure
import gvc.specs.BaseFileSpec
import org.scalatest.ConfigMap

class VerifierSpec extends AnyFunSuite with BaseFileSpec {
  var silicon: Silicon = null

  val testFiles = getFiles("verifier")
    .filter { name => name.endsWith(".c0") && !name.endsWith(".output.c0") }

  for (name <- testFiles) {
    test("test " + name) {
      runVerifierTest(name)
    }
  }

  def runVerifierTest(name: String) = {
    val Success(parsed, _) = Parser.parseProgram(getFile(name).get)
    val sink = new ErrorSink()

    val result = Validator.validateParsed(parsed, sink)
    assert(sink.errors.isEmpty)
    assert(result.isDefined)

    var ir = GraphTransformer.transform(result.get)
    val silver = IRGraphSilver.toSilver(ir)

    assertFile(name.replace(".c0", ".vpr"), silver.toString)

    viper.silicon.state.runtimeChecks.getChecks.clear()
    silicon.verify(silver) match {
      case viper.silver.verifier.Success => ()
      case Failure(errors)               => fail(errors.map(e => e.toString()).mkString("\n"))
    }

    Weaver.weave(ir, silver)
    assertFile(name.replace(".c0", ".output.c0"), GraphPrinter.print(ir, true))
  }

  override protected def beforeAll(config: ConfigMap): Unit = {
    super.beforeAll(config)
    val z3 = Config.resolveToolPath("z3", "Z3_EXE")
    assert(
      !z3.isEmpty,
      "Add z3 to $PATH or configure the Z3_EXE variable with the full path to Z3"
    )

    val reporter = viper.silver.reporter.NoopReporter
    silicon = Silicon.fromPartialCommandLineArguments(
      Seq("--z3Exe", z3),
      reporter,
      Seq()
    )
    silicon.start()
  }

  override protected def afterAll(config: ConfigMap): Unit = {
    super.afterAll(config)
    silicon.stop()
    silicon = null
  }
}
