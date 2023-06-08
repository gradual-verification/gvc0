import org.scalatest.funsuite._
import gvteal.parser._
import fastparse.Parsed.{Success, Failure}

class SpecificationsSpec extends AnyFunSuite {
  test("assert") {
    val Success(List(spec: AssertSpecification), _) = Parser.parseSpec("/*@ assert true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("ensures") {
    val Success(List(spec: EnsuresSpecification), _) = Parser.parseSpec("/*@ ensures true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("requires") {
    val Success(List(spec: RequiresSpecification), _) = Parser.parseSpec("/*@ requires true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("loop_invariant") {
    val Success(List(spec: LoopInvariantSpecification), _) = Parser.parseSpec("/*@ loop_invariant true; @*/")
    assert(spec.value.asInstanceOf[BooleanExpression] == true)
  }

  test("fold") {
    val Success(List(spec: FoldSpecification), _) = Parser.parseSpec("/*@ fold test(x); @*/")
    assert(spec.predicate.name == "test")
    
    val List(x: VariableExpression) = spec.arguments
    assert(x.variable.name == "x")
  }

  test("unfold") {
    val Success(List(spec: UnfoldSpecification), _) = Parser.parseSpec("/*@ unfold test(x); @*/")
    assert(spec.predicate.name == "test")
    
    val List(x: VariableExpression) = spec.arguments
    assert(x.variable.name == "x")
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
      val Failure(_, _, _) = Parser.parseSpec("""
        //@ assert (
          true
        );
      """)
  }

  test("multiple multi-line annotations") {
    val Success(List(_: EnsuresSpecification, _: EnsuresSpecification), _) = Parser.parseSpec("""
      /*@ensures true; @*/
      /*@ensures false; @*/
    """)
  }

  test("multiple specs in a multi-line annotation") {
    val Success(List(_: EnsuresSpecification, _: EnsuresSpecification), _) = Parser.parseSpec("""
      /*@
        ensures true;
        ensures false;
      @*/
    """)
  }

  test("comments inside multi-line annotation") {
    val Success(List(_: AssertSpecification), _) = Parser.parseSpec("""
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

    assert(specs.length == 2)
    assert(specs.forall(_.isInstanceOf[AssertSpecification]))
  }
}