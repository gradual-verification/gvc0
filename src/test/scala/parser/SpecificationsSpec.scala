import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class SpecificationsSpec extends AnyFunSuite {
  test("assert") {
    val Success(List(AssertSpecification(expr)), _) = Parser.parseSpec("/*@ assert true; @*/")
    val BooleanExpression(_, value) = expr
    assert(value == true)
  }

  test("ensures") {
    val Success(List(EnsuresSpecification(expr)), _) = Parser.parseSpec("/*@ ensures true; @*/")
    val BooleanExpression(_, value) = expr
    assert(value == true)
  }

  test("requires") {
    val Success(List(RequiresSpecification(expr)), _) = Parser.parseSpec("/*@ requires true; @*/")
    val BooleanExpression(_, value) = expr
    assert(value == true)
  }

  test("loop_invariant") {
    val Success(List(LoopInvariantSpecification(expr)), _) = Parser.parseSpec("/*@ loop_invariant true; @*/")
    val BooleanExpression(_, value) = expr
    assert(value == true)
  }

  test("multiple multi-line annotations") {
    val Success(List(EnsuresSpecification(_), EnsuresSpecification(_)), _) = Parser.parseSpec("""
      /*@ensures true; @*/
      /*@ensures false; @*/
    """)
  }

  test("multiple specs in a multi-line annotation") {
    val Success(List(EnsuresSpecification(_), EnsuresSpecification(_)), _) = Parser.parseSpec("""
      /*@
        ensures true;
        ensures false;
      @*/
    """)
  }
}