import org.scalatest.funsuite._
import gvteal.parser._
import fastparse.Parsed.{Success, Failure}

class ExpressionsSpec extends AnyFunSuite {
  test("Parse variable") {
    val Success(expr: VariableExpression, _) = Parser.parseExpr("abc")
    assert(expr.variable == "abc")
  }

  test("Identifier position") {
    val Success(expr: VariableExpression, _) = Parser.parseExpr("\nabc\n")
    assert(expr.variable.span.start == SourcePosition(2, 1, 1))
    assert(expr.variable.span.end == SourcePosition(2, 4, 4))
    assert(expr.span == expr.variable.span)
  }

  test("No whitespace in identifiers") {
    val Failure(_, _, _) = Parser.parseExpr("a b")
    val Failure(_, _, _) = Parser.parseExpr("ab c")
  }

  test("Parse decimal number") {
    val Success(IntegerExpression("123", 123, _), _) = Parser.parseExpr("123")
  }

  test("Hex number") {
    val Success(IntegerExpression("0xFF", 0xFF, _), _) = Parser.parseExpr("0xFF")
  }

  test("Hex casing") {
    val Success(IntegerExpression("0XFF", 0xFF, _), _) = Parser.parseExpr(("0XFF"))
    val Success(IntegerExpression("0xff", 0xFF, _), _) = Parser.parseExpr("0xff")
    val Success(IntegerExpression("0Xff", 0xFF, _), _) = Parser.parseExpr("0Xff")
  }

  test("Ignore whitespace") {
    val Success(i: IntegerExpression, _) = Parser.parseExpr("  \t123 \n")
    assert(i == 123)
  }

  test("Do not allow whitespace in decimal literal") {
    val Failure(_, _, _) = Parser.parseExpr("123 456")
  }

  test("String literal") {
    val src = """"test string""""
    val Success(StringExpression(raw, value, _), _) = Parser.parseExpr(src)
    assert(raw == src)
    assert(value == "test string")
  }

  test("Do not allow new lines inside string literals") {
    val Failure(_, _, _) = Parser.parseExpr("\"test\nstring\"")
  }

  test("String literal escapes") {
    val src = """"test\r\n""""
    val Success(StringExpression(raw, value, _), _) = Parser.parseExpr(src)
    assert(raw == src)
    assert(value == "test\r\n")
  }

  test("Boolean literals") {
    val Success(BooleanExpression("true", true, _), _) = Parser.parseExpr("true")
    val Success(BooleanExpression("false", false, _), _) = Parser.parseExpr("false")
  }

  test("Boolean with different case are variables") {
    val cases = List("True", "TRUE", "False", "FALSE")
    for (src <- cases) {
      val Success(expr: VariableExpression, _) = Parser.parseExpr(src)
      assert(expr.variable == src)
    }
  }

  test("NULL literal") {
    val Success(NullExpression("NULL", null, _), _) = Parser.parseExpr("NULL")
  }

  test("Null with difference case is variable") {
    val cases = List("Null", "null", "nuLL")
    for (src <- cases) {
      val Success(expr: VariableExpression, _) = Parser.parseExpr(src)
      assert(expr.variable == src)
    }
  }

  test("alloc expression") {
    val Success(alloc: AllocExpression, _) = Parser.parseExpr("alloc(Test)")
    assert(alloc.valueType.asInstanceOf[NamedType].id == "Test")
  }

  test("alloc_array expression") {
    val Success(alloc: AllocArrayExpression, _) = Parser.parseExpr("alloc_array(Test, 10)")
    assert(alloc.valueType.asInstanceOf[NamedType].id == "Test")
    assert(alloc.length.asInstanceOf[IntegerExpression] == 10)
  }

  test("ternary expression") {
    val Success(expr: TernaryExpression, _) = Parser.parseExpr("true ? 1 : 2")
    assert(expr.condition.asInstanceOf[BooleanExpression] == true)
    assert(expr.ifTrue.asInstanceOf[IntegerExpression] == 1)
    assert(expr.ifFalse.asInstanceOf[IntegerExpression] == 2)
  }

  test("nested ternaries in right side") {
    val Success(t: TernaryExpression, _) = Parser.parseExpr("false ? 1 : true ? 2 : 3")
    assert(t.condition.asInstanceOf[BooleanExpression] == false)
    assert(t.ifTrue.asInstanceOf[IntegerExpression] == 1)
    val nested = t.ifFalse.asInstanceOf[TernaryExpression]
    assert(nested.condition.asInstanceOf[BooleanExpression] == true)
    assert(nested.ifTrue.asInstanceOf[IntegerExpression] == 2)
    assert(nested.ifFalse.asInstanceOf[IntegerExpression] == 3)
  }

  test("nested ternaries in left side") {
    val Success(t: TernaryExpression, _) = Parser.parseExpr("false ? true ? 1 : 2 : 3")
    assert(t.condition.asInstanceOf[BooleanExpression] == false)
    
    val nested = t.ifTrue.asInstanceOf[TernaryExpression]
    assert(nested.condition.asInstanceOf[BooleanExpression] == true)
    assert(nested.ifTrue.asInstanceOf[IntegerExpression] == 1)
    assert(nested.ifFalse.asInstanceOf[IntegerExpression] == 2)
    assert(t.ifFalse.asInstanceOf[IntegerExpression] == 3)
  }

  test("&&") {
    val Success(b: BinaryExpression, _) = Parser.parseExpr("true && false")
    assert(b.left.asInstanceOf[BooleanExpression] == true)
    assert(b.operator == BinaryOperator.LogicalAnd)
    assert(b.right.asInstanceOf[BooleanExpression] == false)
  }

  test("||") {
    val Success(b: BinaryExpression, _) = Parser.parseExpr("true || false")
    assert(b.left.asInstanceOf[BooleanExpression] == true)
    assert(b.operator == BinaryOperator.LogicalOr)
    assert(b.right.asInstanceOf[BooleanExpression] == false)
  }

  test ("&& / || precedence") {
    val Success(or: BinaryExpression, _) = Parser.parseExpr("1 && 2 || 3")
    assert(or.operator == BinaryOperator.LogicalOr)
    assert(or.right.asInstanceOf[IntegerExpression] == 3)

    val and = or.left.asInstanceOf[BinaryExpression]
    assert(and.operator == BinaryOperator.LogicalAnd)
    assert(and.left.asInstanceOf[IntegerExpression] == 1)
    assert(and.right.asInstanceOf[IntegerExpression] == 2)
  }

  test ("&& associativity") {
    val Success(top: BinaryExpression, _) = Parser.parseExpr("1 && 2 && 3")
    val nested = top.left.asInstanceOf[BinaryExpression]
    assert(nested.left.asInstanceOf[IntegerExpression] == 1)
    assert(nested.right.asInstanceOf[IntegerExpression] == 2)
    assert(top.right.asInstanceOf[IntegerExpression] == 3)
  }

  test("&& / == precedence") {
    val Success(and: BinaryExpression, _) = Parser.parseExpr(("1 == 2 && 3 == 4"))
    assert(and.operator == BinaryOperator.LogicalAnd)

    val left = and.left.asInstanceOf[BinaryExpression]
    assert(left.operator == BinaryOperator.Equal)
    assert(left.left.asInstanceOf[IntegerExpression] == 1)
    assert(left.right.asInstanceOf[IntegerExpression] == 2)
    
    val right = and.right.asInstanceOf[BinaryExpression]
    assert(right.operator == BinaryOperator.Equal)
    assert(right.left.asInstanceOf[IntegerExpression] == 3)
    assert(right.right.asInstanceOf[IntegerExpression] == 4)
  }

  test("+ operator is left-associative") {
    // 1 + 2 + 3 should be the same as (1 + 2) + 3
    val Success(top: BinaryExpression, _) = Parser.parseExpr("1 + 2 + 3")
    val nested = top.left.asInstanceOf[BinaryExpression]
    assert(nested.left.asInstanceOf[IntegerExpression] == 1)
    assert(nested.right.asInstanceOf[IntegerExpression] == 2)
    assert(top.right.asInstanceOf[IntegerExpression] == 3)
  }

  test("+ / * precedence") {
    val Success(add: BinaryExpression, _) = Parser.parseExpr("1 * 2 + 3")
    assert(add.operator == BinaryOperator.Add)
    val mult = add.left.asInstanceOf[BinaryExpression]
    assert(mult.operator == BinaryOperator.Multiply)
  }

  test("method call") {
    val Success(expr: InvokeExpression, _) = Parser.parseExpr("test()")
    assert(expr.method == "test")
    assert(expr.arguments.isEmpty)
  }

  test("call with arg") {
    val Success(i: InvokeExpression, _) = Parser.parseExpr("test(123)")
    assert(i.method == "test")
    assert(i.arguments(0).asInstanceOf[IntegerExpression] == 123)
  }

  test("call with multiple args") {
    val Success(i: InvokeExpression, _) = Parser.parseExpr("test(1, \"abc\")")
    assert(i.method == "test")
    assert(i.arguments(0).asInstanceOf[IntegerExpression] == 1)
    assert(i.arguments(1).asInstanceOf[StringExpression] == "abc")
  }

  test("dot member") {
    val Success(m: MemberExpression, _) = Parser.parseExpr("abc.def")
    assert(m.field == "def")
    assert(!m.isArrow)
    assert(m.parent.asInstanceOf[VariableExpression].variable == "abc")
  }

  test("pointer member") {
    val Success(expr: MemberExpression, _) = Parser.parseExpr("abc->def")
    assert(expr.field == "def")
    assert(expr.isArrow)
    assert(expr.parent.asInstanceOf[VariableExpression].variable == "abc")
  }

  test("member of method call") {
    val Success(expr: MemberExpression, _) = Parser.parseExpr("read().output")
    assert(expr.field == "output")
    assert(!expr.isArrow)

    val invoke = expr.parent.asInstanceOf[InvokeExpression]
    assert(invoke.method == "read")
  }

  test("array index") {
    val Success(expr: IndexExpression, _) = Parser.parseExpr(("arr[0]"))
    assert(expr.index.asInstanceOf[IntegerExpression] == 0)
    assert(expr.parent.asInstanceOf[VariableExpression].variable == "arr")
  }

  test("unary not") {
    val Success(expr: UnaryExpression, _) = Parser.parseExpr("!test")
    assert(expr.operator == UnaryOperator.Not)
    assert(expr.operand.asInstanceOf[VariableExpression].variable == "test")
  }

  test("repeated unary operators") {
    val Success(top: UnaryExpression, _) = Parser.parseExpr("!!abc")
    assert(top.operator == UnaryOperator.Not)
    val nested = top.operand.asInstanceOf[UnaryExpression]
    assert(nested.operator == UnaryOperator.Not)
    assert(nested.operand.asInstanceOf[VariableExpression].variable == "abc")
  }

  test("unary operators right-associative") {
    val Success(outer: UnaryExpression, _) = Parser.parseExpr("~-1")
    assert(outer.operator == UnaryOperator.BitwiseNot)
    val inner = outer.operand.asInstanceOf[UnaryExpression]
    assert(inner.operator == UnaryOperator.Negate)
    assert(inner.operand.asInstanceOf[IntegerExpression] == 1)
  }

  test("\\result") {
    val Success(result, _) = Parser.parseExpr("\\result")
    assert(result.isInstanceOf[ResultExpression])
  }

  test("\\length") {
    val Success(length: LengthExpression, _) = Parser.parseExpr("\\length(a)")
    val varRef = length.value.asInstanceOf[VariableExpression]
    assert(varRef.variable.name === "a")
  }
}