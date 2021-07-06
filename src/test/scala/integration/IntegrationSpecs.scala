package gvc.integration

import gvc.parser._
import org.scalatest.funsuite._
import java.io.File
import scala.io.Source
import fastparse.Parsed.{Success, Failure}
import gvc.analyzer.Resolver
import gvc.analyzer.ErrorSink
import gvc.analyzer.ResolvedProgram

class IntegrationSpecs extends AnyFunSuite {
  // The test files are copied with some modifications in the test header
  // from tests/fp-basic in the cc0 repository
  val testFiles = List(
    "anno1.c0",
    "anno2.c0",
    "anno3.c0",
    "anno4.c0",
    "anno5.c0",
    "anno6.c0",
    "anno7.c0",
    "anno8.c0",
    "anno9.c0",
    "annoa.c0",
    "annob.c0",
    // "annoc.c0", TODO: Debug this test
    "annod.c0",
    // "annoe.c0", TODO: well-formedness check
    "annof.c0",
    // "annog.c0", TODO: \length assertion
    "annoh.c0",
    "annoi.c0",
    // "annoj.c0", TODO: dereference operator
    // "annok.c0", TODO: deref
    "arith01.c0",
    "arith02.c0",
    // "arith03.c0", (modulo)
    // "arith04.c0",
    // "arith05.c0",
    // "arith06.c0",
    // "arith07.c0",
    // "arith08.c0", (bit shift)
    // "arith09.c0",
    // "arith10.c0",
    "arrayinit1.c0",
    "brackets0.c0",
    "brackets1.c0",
    // "cast07.c0", TODO: deref
    "compound1.c0",
    // "compound2.c0", (modulo)
    // "compound3.c0", (bit shift)
    // "compound4.c0",
    "compound5.c0",
    // "compound6.c0", (modulo)
    // "compound7.c0", (bit shift)
    // "compound8.c0",
    "cond1.c0",
    "cond2.c0",
    // "condnull1.c0", TODO: deref
    "condnull2.c0",
    "deref00.c0",
    // "empty.c0", TODO: how to handle empty?
    "empty2.c0",
    "forloop1.c0",
    // "forloop2.c0", TODO: well-formedness
    // "forloop3.c0", TODO: BUG?
    "forloop4.c0",
    // "if0.c0", TODO: deref
    // "if1.c0", TODO: deref
    // "if2.c0", TODO: deref
    // "if3.c0", TODO: deref
    // "init01.c0", TODO: use-before-assign
    "init02.c0",
    // "init03.c0", TODO: use-before-assign
    "init04.c0",
    "init05.c0",
    "init06.c0",
    "init07.c0",
    "lexer01.c0",
    // "lexer02.c0", TODO: big numbers
    // "lexer03.c0", TODO: big numbers
    // "lexer04.c0", TODO: big numbers
    "lexer05.c0",
    // "lexer06.c0", TODO: single-line comment cannot end at EOF?
    "lexer07.c0",
    "lexer08.c0",
    "lexer09.c0",
    "lexer10.c0",
    // "lexer11.c0", TODO: BUG with escapes?
    "lexer12.c0",
    "lexer13.c0",
    // "lexer14.c0", TODO: extend whitespace
    // "lexer15.c0", TODO: BUG with escapes?
    "lexer16.c0",
    "lexer17.c0",
    "lexer18.c0",
    // "libfuns1.c0", TODO: #use
    // "libfuns2.c0", TODO: #use
    "multidecls1.c0",
    "multidecls2.c0",
    // "multidecls3.c0", TODO: type check args
    // "multidecls4.c0", TODO: type check args
    // "multidecls5.c0", TODO: type check args
    "multidecls6.c0",
    // "multidecls7.c0", TODO: no intersecting typedefs/methods
    // "multidecls8.c0", TODO: no intersecting typedefs/methods
    "multidecls9.c0",
    "multidecls10.c0",
    "multidecls11.c0",
    "multidecls12.c0",
    // "multidecls13.c0", TODO: type check args
    "multidecls14.c0",
    // "multidecls15.c0", TODO: \result
    // "multidecls16.c0", TODO: no intersecting typedefs/methods
    "null1.c0",
    "null2.c0",
    // "overload01.c0", TODO: BUG escape handling?
    // "parallel-decl.c0", TODO: big numbers
    "params1.c0",
    "params2.c0",
    // "pragma1.c0", TODO: #use
    // "safediv.c0", (modulo)
    // "semi.c0", TODO: parse while(true); as a parse error
    "shadow1.c0",
    "shadow2.c0",
    // "shadow3.c0", TODO: no intersecting type/variable names
    "shadow4.c0",
    "shadow5.c0",
    // "shadow6.c0", TODO: no calling variables
    "shadow7.c0",
    "shadow8.c0",
    "shadow9.c0",
    // "shadowa.c0", TODO: no calling variables
    "signed.c0",
    // "starplusplus1.c0", TODO: deref
    // "starplusplus2.c0", TODO: deref
    // "starplusplus3.c0", TODO: deref
    // "starplusplus4.c0", TODO: deref
    "struct-undef1.c0",
    // "struct-undef2.c0", TODO: undeclared structs
    // "struct-undef3.c0", TODO: undeclared structs
    "struct-undef4.c0",
    "typenames.c0",
    // "typenames2.c0", TODO: no intersecting type/method names
    // "undefined1.c0", TODO: how to handle no main method?
    // "undefined2.c0", TODO: how to handle undefined methods?
    "undefined3.c0",
    "unsafeopt.c0",
    "unsafeopt2.c0",
    "usetest.c0",
    // "usetest0.c0", TODO: #use
    // "void.c0", TODO: void
  )

  for (file <- testFiles) {
    test("test " + file) {
      val src = Source.fromResource("fp-basic/" + file).mkString
      val result = runIntegrationTest(src)
      
      if (src.startsWith("//test error")) {
        assert(result.isInstanceOf[ParseError])
      } else if (src.startsWith("//test resolve_error")) {
        assert(result.isInstanceOf[ResolverError])
      } else {
        assert(result.isInstanceOf[ValidProgram])
      }
    }
  }

  def runIntegrationTest(source: String): IntegrationResult = {
    Parser.parseProgram(source) match {
      case fail: Failure => ParseError(fail.trace().msg)
      case Success(parsed, _) => {
        val sink = new ErrorSink()
        val result = Resolver.resolveProgram(parsed, sink)
        sink.errors match {
          case Nil => ValidProgram(result)
          case _ => ResolverError(sink.errors.map(_.message))
        }
      }
    }
  }

  sealed trait IntegrationResult
  case class ParseError(message: String) extends IntegrationResult
  case class ResolverError(messages: List[String]) extends IntegrationResult
  case class ValidProgram(program: ResolvedProgram) extends IntegrationResult
}

