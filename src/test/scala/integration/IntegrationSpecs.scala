package gvc.integration

import gvc.parser._
import org.scalatest.funsuite._
import java.io.File
import scala.io.Source
import fastparse.Parsed.{Success, Failure}
import gvc.analyzer.{Resolver, ErrorSink, TypeChecker, AssignmentValidator}
import gvc.analyzer.ReturnValidator
import gvc.transformer.Transformer
import gvc.transformer.CNaughtPrinter
import gvc.transformer.IR

class IntegrationSpecs extends AnyFunSuite {
  val testDirs = List(
    // The test files are copied with some modifications in the test header
    // from tests/fp-basic in the cc0 repository
    "fp-basic/",
    "cases/",
    "ir/",
  )

  val exclusions = Set(
    //"cases/struct_5.c0", // TODO: Struct flattening

    // PARSING
    // TODO: fix big number handling
    "fp-basic/lexer02.c0",
    "fp-basic/lexer03.c0",
    "fp-basic/lexer04.c0",
    "fp-basic/parallel-decl.c0",
    // TODO: while(true); should be a parse error
    "fp-basic/semi.c0",

    // RESOLVING
    // TODO: implement #use
    "fp-basic/libfuns1.c0",
    "fp-basic/libfuns2.c0",
    "fp-basic/pragma1.c0",
    "fp-basic/usetest0.c0",

    // TYPE CHECKING

    // WELL-FORMEDNESS
    
    // UNSUPPORTED STUFF
    // Modulus operator
    "fp-basic/arith03.c0",
    "fp-basic/arith04.c0",
    "fp-basic/arith05.c0",
    "fp-basic/arith06.c0",
    "fp-basic/arith07.c0",
    "fp-basic/compound2.c0",
    "fp-basic/compound6.c0",
    "fp-basic/safediv.c0",
    // Bit shifts
    "fp-basic/arith08.c0",
    "fp-basic/arith09.c0",
    "fp-basic/arith10.c0",
    "fp-basic/compound3.c0",
    "fp-basic/compound4.c0",
    "fp-basic/compound5.c0",
    "fp-basic/compound7.c0",
    "fp-basic/compound8.c0",
    "fp-basic/undefined1.c0", // we don't error on undefined main
    "fp-basic/undefined2.c0", // we don't error on undefined functions
    "fp-basic/empty.c0", // we don't error on empty file
  )

  val testFiles = testDirs.flatMap(dir =>
    new File(getClass().getResource("/" + dir).getFile()).listFiles()
      map { file => (dir + file.getName().toLowerCase(), file) }
      filterNot { case (name, _) => exclusions.contains(name) }
      filterNot { case (name, _) => name.endsWith(".ir.c0") })

  for ((name, file) <- testFiles) {
    test("test " + name) {
      val irFile = new File(file.getParentFile(), file.getName().replace(".c0", ".ir.c0"))

      val src = Source.fromFile(file).mkString
      val irSrc = if (irFile.exists()) Some(Source.fromFile(irFile).mkString) else None
      val result = runIntegrationTest(src, irSrc)
      
      if (src.startsWith("//test error")) {
        assert(result.isInstanceOf[ParseError])
      } else if (src.startsWith("//test resolve_error")) {
        assert(result.isInstanceOf[ResolverError])
      } else if (src.startsWith("//test type_error")) {
        assert(result.isInstanceOf[TypeError])
      } else if (src.startsWith("//test validation_error")) {
        assert(result.isInstanceOf[ValidationError])
      } else {
        assert(result == ValidProgram)
      }
    }
  }

  def runIntegrationTest(source: String, expectedIR: Option[String]): IntegrationResult = {
    Parser.parseProgram(source) match {
      case fail: Failure => ParseError(fail.trace().longMsg)
      case Success(parsed, _) => {
        val sink = new ErrorSink()
        val result = Resolver.resolveProgram(parsed, sink)
        if (!sink.errors.isEmpty) {
          ResolverError(sink.errors.map(_.message))
        } else {
          TypeChecker.check(result, sink)
          if (!sink.errors.isEmpty) {
            TypeError(sink.errors.map(_.message))
          } else {
            AssignmentValidator.validate(result, sink)
            ReturnValidator.validate(result, sink)
            if (!sink.errors.isEmpty) {
              ValidationError(sink.errors.map(_.message))
            } else {
              var ir = Transformer.programToIR(result)
              val methods = ir.methods.collect { case m: IR.MethodImplementation => m }
                .map(CNaughtPrinter.printMethod(_))
                .mkString("\n")

              if (expectedIR.isDefined)
                assert(expectedIR.get == methods)
              ValidProgram
            }
          }
        }
      }
    }
  }

  sealed trait IntegrationResult
  case class ParseError(message: String) extends IntegrationResult
  case class ResolverError(messages: List[String]) extends IntegrationResult
  case class TypeError(messages: List[String]) extends IntegrationResult
  case class ValidationError(messages: List[String]) extends IntegrationResult
  case object ValidProgram extends IntegrationResult
}

