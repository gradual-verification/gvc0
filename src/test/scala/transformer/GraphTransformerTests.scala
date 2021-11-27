package transformer

import scala.io.Source
import gvc.parser.Parser
import fastparse.Parsed
import gvc.analyzer.ErrorSink
import gvc.analyzer.Validator
import gvc.transformer.GraphTransformer
import gvc.transformer.GraphPrinter
import org.scalatest.funsuite.AnyFunSuite

class GraphTransformerTests extends AnyFunSuite {
  val testFiles = List(
    "ir/assert_1",
    "ir/assert_2",
    "ir/for",
    "ir/increment",
    "ir/logical",
    "ir/logical_2",
    "ir/struct_embed",
    "ir/ternary",
    "ir/while",
  )

  for (name <- testFiles) {
    test("test " + name) {
      val src = Source.fromResource(name + ".c0").mkString
      val expected = Source.fromResource(name + ".ir.c0").mkString


      val Parsed.Success(parsed, _) = Parser.parseProgram(src)
      val errors = new ErrorSink()
      val resolved = Validator.validateParsed(parsed, errors)
      assert(errors.errors.isEmpty)
      assert(resolved.isDefined)

      val ir = GraphTransformer.transform(resolved.get)
      val printed = GraphPrinter.print(ir)
      assert(printed == expected)
    }
  }
}