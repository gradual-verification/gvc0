package gvc.weaver

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

    new Weaver(c0, silver).weave()
    val output = GraphPrinter.print(c0)
    assert(output ==
      """|int main();
         |
         |int main()
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
        val result = Validator.validateParsed(parsed, sink)
        assert(sink.errors.isEmpty)
        assert(result.isDefined)

        val ir = GraphTransformer.transform(result.get)
        val silver = IRGraphSilver.toSilver(ir)
        (ir, silver)
      }
    }
  }
}

