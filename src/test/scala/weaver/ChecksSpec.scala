package gvc.weaver

import gvc.weaver.CheckExpression._
import org.scalatest.funsuite.AnyFunSuite

class ChecksSpec extends AnyFunSuite {
  test("guard field reference") {
    val field = Field(Var("test"), "Test", "value")
    val guard = field.guard
    assert(guard == Some(Not(Eq(Var("test"), NullLit))))
  }

  test("guard nested field reference") {
    // a->b->c
    // a != NULL && a->b != NULL
    val value = Field(Field(Var("a"), "Test", "b"), "Test", "c")
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Not(Eq(Field(Var("a"), "Test", "b"), NullLit))
    )))
  }

  test("guard pointer deref") {
    val field = Deref(Var("test"))
    val guard = field.guard
    assert(guard == Some(Not(Eq(Var("test"), NullLit))))
  }

  test("guard both sides of addition") {
    val value = Add(Deref(Var("a")), Field(Var("b"), "Test", "value"))
    assert(value.guard == Some(And(Not(Eq(Var("a"), NullLit)), Not(Eq(Var("b"), NullLit)))))
  }

  test("guard one side of addition") {
    val value = Add(IntLit(1), Field(Var("b"), "Test", "value"))
    assert(value.guard == Some(Not(Eq(Var("b"), NullLit))))
  }

  test("guard and") {
    val value = And(Deref(Var("a")), Deref(Var("b")))
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Not(Eq(Var("b"), NullLit))
    )))
  }

  test("guard negated and") {
    val value = Not(And(Deref(Var("a")), Deref(Var("b"))))
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Not(Eq(Var("b"), NullLit))
    )))
  }

  test("guard or") {
    // *a || *b
    // (a != NULL) && (*a || b != NULL)

    val value = Or(Deref(Var("a")), Deref(Var("b")))
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Or(Deref(Var("a")), Not(Eq(Var("b"), NullLit)))
    )))
  }

  test("guard negated or") {
    // !(*a || *b)
    // (a != NULL) && (*a || b != NULL)
    // Negation does not change what is evaluated

    val value = Not(Or(Deref(Var("a")), Deref(Var("b"))))
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Or(Deref(Var("a")), Not(Eq(Var("b"), NullLit)))
    )))
  }

  test("guard or RHS") {
    // a || *b
    // a || b != NULL
    val value = Or(Var("a"), Deref(Var("b")))
    assert(value.guard == Some(
      Or(Var("a"), Not(Eq(Var("b"), NullLit)))
    ))
  }

  test("guard or LHS") {
    // *a || b
    // a != NULL
    val value = Or(Deref(Var("a")), Var("b"))
    assert(value.guard == Some(
      Not(Eq(Var("a"), NullLit))
    ))
  }

  test("guard conditional") {
    // *a ? *b : *c
    // a != NULL && (*a ? b != NULL : c != NULL)
    val value = Cond(Deref(Var("a")), Deref(Var("b")), Deref(Var("c")))
    assert(value.guard == Some(And(
      Not(Eq(Var("a"), NullLit)),
      Cond(Deref(Var("a")),
        Not(Eq(Var("b"), NullLit)),
        Not(Eq(Var("c"), NullLit))
      )
    )))
  }

  test("guard conditional - only condition") {
    // *a ? b : c
    // a != NULL
    val value = Cond(Deref(Var("a")), Var("b"), Var("c"))
    assert(value.guard == Some(
      Not(Eq(Var("a"), NullLit)),
    ))
  }

  test("guard conditional - only true branch") {
    // a ? *b : c
    // !a || b != NULL
    val value = Cond(Var("a"), Deref(Var("b")), Var("c"))
    assert(value.guard == Some(Or(
      Not(Var("a")),
      Not(Eq(Var("b"), NullLit)),
    )))
  }

  test("guard conditional - only false branch") {
    // a ? b : *c
    // a || b != NULL
    val value = Cond(Var("a"), Var("b"), Deref(Var("c")))
    assert(value.guard == Some(Or(
      Var("a"),
      Not(Eq(Var("c"), NullLit)),
    )))
  }
}