package gvc.permutation

import org.scalatest.funsuite.AnyFunSuite

import fastparse.Parsed.{Success, Failure}
import gvc.analyzer.ErrorSink
import gvc.analyzer.Validator
import gvc.transformer.GraphTransformer
import gvc.specs.BaseFileSpec
import gvc.transformer.GraphPrinter

class BaselineSpec extends AnyFunSuite with BaseFileSpec {
  val testFiles = getFiles("baseline")
    .filter { name => name.endsWith(".c0") && !name.endsWith(".baseline.c0") }

  for (name <- testFiles) {
    test("test " + name) {
      val ir = createProgram(getFile(name).get)
      BaselineChecker.check(ir)

      val output = GraphPrinter.print(ir, false)
      assertFile(name.replace(".c0", ".baseline.c0"), output)
    }
  }

  def createProgram(source: String) = {
    gvc.parser.Parser.parseProgram(source) match {
      case _: Failure => fail("could not parse")
      case Success(parsed, _) => {
        val sink = new ErrorSink()
        val result = Validator.validateParsed(parsed, List(), sink)
        assert(sink.errors.isEmpty)
        assert(result.isDefined)

        GraphTransformer.transform(result.get)
      }
    }
  }
}
