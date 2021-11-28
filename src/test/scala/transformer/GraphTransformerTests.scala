package transformer

import scala.io.Source
import gvc.parser.Parser
import fastparse.Parsed
import gvc.analyzer.ErrorSink
import gvc.analyzer.Validator
import gvc.transformer.GraphTransformer
import gvc.transformer.GraphPrinter
import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer.IRGraphSilver
import java.io.File
import java.io.PrintWriter

class GraphTransformerTests extends AnyFunSuite {
  val UPDATE = false

  val testFiles = List(
    "ir/assert_1",
    "ir/assert_2",
    "ir/for",
    "ir/increment",
    "ir/logical",
    "ir/logical_2",
    "ir/specs",
    "ir/struct_embed",
    "ir/ternary",
    "ir/while",
    "viper/call",
    "viper/char",
    "viper/field",
    "viper/imprecise_1",
    "viper/imprecise_2",
    "viper/imprecise_3",
    "viper/int_pointer",
    "viper/main",
    "viper/negate",
    "viper/not",
    "viper/predicate_1",
    "viper/specs",
    "viper/while",
  )

  def getFile(name: String): Option[String] = getClass().getResource("/" + name) match {
    case null => None
    case url => Some(Source.fromURL(url).mkString)
  }

  def assertFile(name: String, actual: String): Unit = {
    getFile(name).foreach { expected =>
      if (UPDATE) {
        if (actual != expected)
          writeFile(name, actual)
      } else {
        assert(actual == expected)
      }
    }
  }

  def writeFile(name: String, value: String): Unit = {
    val url = getClass().getResource("/" + name)
    new PrintWriter(new File(url.getFile())) {
      write(value)
      close()
    }
  }

  for (name <- testFiles) {
    test("test " + name) {
      val src = getFile(name + ".c0").get

      val Parsed.Success(parsed, _) = Parser.parseProgram(src)
      val errors = new ErrorSink()
      val resolved = Validator.validateParsed(parsed, errors)
      assert(errors.errors.isEmpty)
      assert(resolved.isDefined)

      val ir = GraphTransformer.transform(resolved.get)
      assertFile(name + ".ir.c0", GraphPrinter.print(ir))

      val silver = IRGraphSilver.toSilver(ir).toString()
      assertFile(name + ".vpr", silver.toString())
    }
  }
}