package gvc.integration

import gvc.parser._
import org.scalatest.funsuite._
import java.io.File
import scala.io.Source
import fastparse.Parsed.{Success, Failure}
import gvc.analyzer.{Resolver, ErrorSink, ResolvedProgram, TypeChecker}

class IntegrationSpecs extends AnyFunSuite {
  val testDirs = List(
    // The test files are copied with some modifications in the test header
    // from tests/fp-basic in the cc0 repository
    "fp-basic/",
    "cases/"
  )

  val exclusions = Set(
    // PARSING
    // TODO: fix big number handling
    "fp-basic/lexer02.c0",
    "fp-basic/lexer03.c0",
    "fp-basic/lexer04.c0",
    "fp-basic/parallel-decl.c0",
    // TODO: while(true); should be a parse error
    "fp-basic/semi.c0",
    // TODO: Fix precedence of ++ and *
    "fp-basic/starplusplus1.c0",
    // TODO: Fix precedence of -- and *
    "fp-basic/starplusplus4.c0",
    //TODO: \length assertions
    "fp-basic/annog.c0",
    // TODO: \result assertions
    "fp-basic/multidecls15.c0",

    // RESOLVING
    // TODO: implement #use
    "fp-basic/libfuns1.c0",
    "fp-basic/libfuns2.c0",
    "fp-basic/pragma1.c0",
    "fp-basic/usetest0.c0",

    // TYPE CHECKING
    // TODO: Don't allow returning void
    "fp-basic/void.c0",

    // WELL-FORMEDNESS
    // TODO: check for deref NULL
    "fp-basic/condnull1.c0",
    // TODO: don't assign to variables in post-conditions (without \old)
    "fp-basic/annoe.c0",
    // TODO: don't declare variable in incrementor (maybe resolver?)
    "fp-basic/forloop2.c0",
    // TODO: check for use-before-assign
    "fp-basic/init01.c0",
    "fp-basic/init03.c0",
    
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
      filterNot { case (name, _) => exclusions.contains(name) })

  for ((name, file) <- testFiles) {
    test("test " + name) {
      val src = Source.fromFile(file).mkString
      val result = runIntegrationTest(src)
      
      if (src.startsWith("//test error")) {
        assert(result.isInstanceOf[ParseError])
      } else if (src.startsWith("//test resolve_error")) {
        assert(result.isInstanceOf[ResolverError])
      } else if (src.startsWith("//test type_error")) {
        assert(result.isInstanceOf[TypeError])
      } else {
        assert(result == ValidProgram)
      }
    }
  }

  def runIntegrationTest(source: String): IntegrationResult = {
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
            ValidProgram
          }
        }
      }
    }
  }

  sealed trait IntegrationResult
  case class ParseError(message: String) extends IntegrationResult
  case class ResolverError(messages: List[String]) extends IntegrationResult
  case class TypeError(messages: List[String]) extends IntegrationResult
  case object ValidProgram extends IntegrationResult
}

