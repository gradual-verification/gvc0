import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class SpecExprificationsSpecExpr extends AnyFunSuite {
  test("assert") {
    val Success(List(spec: AssertSpecExprification), _) = Parser.parseSpecExpr("/*@ assert true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("ensures") {
    val Success(List(spec: EnsuresSpecExprification), _) = Parser.parseSpecExpr("/*@ ensures true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("requires") {
    val Success(List(spec: RequiresSpecExprification), _) = Parser.parseSpecExpr("/*@ requires true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("loop_invariant") {
    val Success(List(spec: LoopInvariantSpecExprification), _) = Parser.parseSpecExpr("/*@ loop_invariant true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("fold") {
    val Success(List(spec: FoldSpecExprification), _) = Parser.parseSpecExpr("/*@ fold test(x); @*/")
    assert(spec.predicate.name == "test")
    
    val List(x: VariableExpression) = spec.arguments
    assert(x.variable.name == "x")
  }

  test("unfold") {
    val Success(List(spec: UnfoldSpecExprification), _) = Parser.parseSpecExpr("/*@ unfold test(x); @*/")
    assert(spec.predicate.name == "test")
    
    val List(x: VariableExpression) = spec.arguments
    assert(x.variable.name == "x")
  }

  test("single-line annotation") {
    val Success(List(s), _) = Parser.parseSpecExpr("//@ ensures true;")
    assert(s.isInstanceOf[EnsuresSpecExprification])
  }

  test("single-line annotation followed by single-line comment") {
    val Success(List(s), _) = Parser.parseSpecExpr("""
      //@ ensures true;
      // test comment
    """)
    assert(s.isInstanceOf[EnsuresSpecExprification])
  }

  test("do not allow multi-line expressions inside single-line annotations") {
      val Failure(_, _, _) = Parser.parseSpecExpr("""
        //@ assert (
          true
        );
      """)
  }

  test("multiple multi-line annotations") {
    val Success(List(_: EnsuresSpecExprification, _: EnsuresSpecExprification), _) = Parser.parseSpecExpr("""
      /*@ensures true; @*/
      /*@ensures false; @*/
    """)
  }

  test("multiple specs in a multi-line annotation") {
    val Success(List(_: EnsuresSpecExprification, _: EnsuresSpecExprification), _) = Parser.parseSpecExpr("""
      /*@
        ensures true;
        ensures false;
      @*/
    """)
  }

  test("comments inside multi-line annotation") {
    val Success(List(_: AssertSpecExprification), _) = Parser.parseSpecExpr("""
    /*@
      assert /* comment */ true;
      // comment
    @*/
    """)
  }

  test("treat @ in annotation as whitespace") {
    //val Success(List(AssertSpecExprification(_), AssertSpecExprification(_)), _) =
    val Success(specs, _) = Parser.parseSpecExpr("""
      //@@ assert @true@;@
      /*@ assert@true;@@*/
    """)

    assert(specs.length == 2)
    assert(specs.forall(_.isInstanceOf[AssertSpecExprification]))
  }
}