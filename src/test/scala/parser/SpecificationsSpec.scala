import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class SpecificationsSpec extends AnyFunSuite {
  test("assert") {
    val Success(List(AssertSpecification(expr)), _) = Parser.parseSpec("/*@ assert true; @*/")
    assert(expr.asInstanceOf[BooleanExpression] == true)
  }

  test("ensures") {
    val Success(List(EnsuresSpecification(expr)), _) = Parser.parseSpec("/*@ ensures true; @*/")
    assert(expr.asInstanceOf[BooleanExpression] == true)
  }

  test("requires") {
    val Success(List(RequiresSpecification(expr)), _) = Parser.parseSpec("/*@ requires true; @*/")
    assert(expr.asInstanceOf[BooleanExpression] == true)
  }

  test("loop_invariant") {
    val Success(List(LoopInvariantSpecification(expr)), _) = Parser.parseSpec("/*@ loop_invariant true; @*/")
    assert(expr.asInstanceOf[BooleanExpression] == true)
  }

  test("single-line annotation") {
    val Success(List(s), _) = Parser.parseSpec("//@ ensures true;")
    assert(s.isInstanceOf[EnsuresSpecification])
  }

  test("single-line annotation followed by single-line comment") {
    val Success(List(s), _) = Parser.parseSpec("""
      //@ ensures true;
      // test comment
    """)
    assert(s.isInstanceOf[EnsuresSpecification])
  }

  test("do not allow multi-line expressions inside single-line annotations") {
      val Failure(_) = Parser.parseSpec("""
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