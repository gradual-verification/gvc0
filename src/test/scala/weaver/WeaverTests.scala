package gvc.weaver

import viper.silver.{ast=>vpr}
import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer._
import gvc.analyzer._
import fastparse.Parsed.{Success,Failure}

class WeaverTests extends AnyFunSuite {

  test("resolve empty method") {
    val (c0, silver) = createProgram(
      """
      int main()
      {
        return 0;
      }
      """
    )

    val woven = Weaver.weave(c0, silver)
    val main = woven.methods.find(_.name == "main").get.asInstanceOf[IR.MethodImplementation]
    val output = CNaughtPrinter.printMethod(main, false)

    assert(output ==
      """|int main()
         |{
         |  return 0;
         |}
         |""".stripMargin)
  }

  def createProgram(source: String) = {
    gvc.parser.Parser.parseProgram(source) match {
      case _: Failure => fail("could not parse")
      case Success(parsed, _) => {
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

        val ir = Transformer.programToIR(result)
        val silver = SilverOutput.program(ir)
        (ir, silver)
      }
    }
  }
}

