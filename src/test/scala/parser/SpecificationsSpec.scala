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

  test("single-line annotation") {
    val Success(List(EnsuresSpecification(_)), _) = Parser.parseSpec("//@ ensures true;")
  }

  test("single-line annotation followed by single-line comment") {
    val Success(List(EnsuresSpecification(_)), _) = Parser.parseSpec("""
      //@ ensures true;
      // test comment
    """)
  }

  test("do not allow multi-line expressions inside single-line annotations") {
      val Failure(_, _, _) = Parser.parseSpec("""
        //@ assert (
          true
        );
      """)
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

  test("comments inside multi-line annotation") {
    val Success(List(AssertSpecification(_)), _) = Parser.parseSpec("""
    /*@
      assert /* comment */ true;
      // comment
    @*/
    """)
  }

  test("treat @ in annotation as whitespace") {
    //val Success(List(AssertSpecification(_), AssertSpecification(_)), _) = 
    val Success(specs, _) = Parser.parseSpec("""
      //@@ assert @true@;@
      /*@ assert@true;@@*/
    """)

    val List(AssertSpecification(_), AssertSpecification(_)) = specs
  }
}