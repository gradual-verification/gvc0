import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class ExpressionsSpec extends AnyFunSuite {
  test("Parse variable") {
    val Success(VariableExpression(Identifier(name)), _) = Parser.parseExpr("abc")
    assert(name == "abc")
  }

  test("No whitespace in identifiers") {
    val Failure(_) = Parser.parseExpr("a b")
    val Failure(_) = Parser.parseExpr("ab c")
  }

  test("Parse decimal number") {
    val Success(IntegerExpression("123", 123), _) = Parser.parseExpr("123")
  }

  test("Hex number") {
    val Success(IntegerExpression("0xFF", 0xFF), _) = Parser.parseExpr("0xFF")
  }

  test("Hex casing") {
    val Success(IntegerExpression("0XFF", 0xFF), _) = Parser.parseExpr(("0XFF"))
    val Success(IntegerExpression("0xff", 0xFF), _) = Parser.parseExpr("0xff")
    val Success(IntegerExpression("0Xff", 0xFF), _) = Parser.parseExpr("0Xff")
  }

  test("Ignore whitespace") {
    val Success(IntegerExpression("123", 123), _) = Parser.parseExpr("  \t123 \n")
  }

  test("Do not allow whitespace in decimal literal") {
    val Failure(_) = Parser.parseExpr("123 456")
  }

  test("String literal") {
    val src = """"test string""""
    val Success(StringExpression(raw, value), _) = Parser.parseExpr(src)
    assert(raw == src)
    assert(value == "test string")
  }

  test("Do not allow new lines inside string literals") {
    val Failure(_) = Parser.parseExpr("\"test\nstring\"")
  }

  test("String literal escapes") {
    val src = """"test\r\n""""
    val Success(StringExpression(raw, value), _) = Parser.parseExpr(src)
    assert(raw == src)
    assert(value == "test\r\n")
  }

  test("Boolean literals") {
    val Success(BooleanExpression("true", true), _) = Parser.parseExpr("true")
    val Success(BooleanExpression("false", false), _) = Parser.parseExpr("false")
  }

  test("Boolean with different case are variables") {
    val cases = List("True", "TRUE", "False", "FALSE")
    for (src <- cases) {
      val Success(VariableExpression(Identifier(name)), _) = Parser.parseExpr(src)
      assert(name == src)
    }
  }

  test("NULL literal") {
    val Success(NullExpression("NULL", null), _) = Parser.parseExpr("NULL")
  }

  test("Null with difference case is variable") {
    val cases = List("Null", "null", "nuLL")
    for (src <- cases) {
      val Success(VariableExpression(Identifier(name)), _) = Parser.parseExpr(src)
      assert(name == src)
    }
  }

  test("alloc expression") {
    val Success(AllocExpression(valueType), _) = Parser.parseExpr("alloc(Test)")
    val NamedType(Identifier(name)) = valueType
    assert(name == "Test")
  }

  test("alloc_array expression") {
    val Success(AllocArrayExpression(valueType, lenExpr), _) =
      Parser.parseExpr("alloc_array(Test, 10)")

    val NamedType(Identifier(name)) = valueType
    assert(name == "Test")

    val IntegerExpression(_, len) = lenExpr
    assert(len == 10)
  }

  test("ternary expression") {
    val Success(TernaryExpression(condExpr, ifTrueExpr, ifFalseExpr), _) = Parser.parseExpr("true ? 1 : 2")
    val BooleanExpression(_, cond) = condExpr
    assert(cond == true)

    val IntegerExpression(_, ifTrue) = ifTrueExpr
    val IntegerExpression(_, ifFalse) = ifFalseExpr
    assert(ifTrue == 1)
    assert(ifFalse == 2)
  }

  test("nested ternaries") {
    val Success(
      TernaryExpression(
        BooleanExpression(_, false),
        IntegerExpression(_, 1),
        TernaryExpression(
          BooleanExpression(_, true),
          IntegerExpression(_, 2),
          IntegerExpression(_, 3)
        )
      ), _
    ) = Parser.parseExpr("false ? 1 : true ? 2 : 3")

    val Success(
      TernaryExpression(
        BooleanExpression(_, false),
        TernaryExpression(
          BooleanExpression(_, true),
          IntegerExpression(_, 1),
          IntegerExpression(_, 2)
        ),
        IntegerExpression(_, 3),
      ), _
    ) = Parser.parseExpr("false ? true ? 1 : 2 : 3")
  }

  test("&&") {
    val Success(BinaryExpression(BooleanExpression(_, true), op, BooleanExpression(_, false)), _) =
      Parser.parseExpr("true && false")
    assert(op == BinaryOperator.LogicalAnd)
  }

  test("||") {
    val Success(BinaryExpression(BooleanExpression(_, true), op, BooleanExpression(_, false)), _) =
      Parser.parseExpr("true || false")
    assert(op == BinaryOperator.LogicalOr)
  }

  test ("&& / || precedence") {
    val Success(BinaryExpression(l1, op1, r1), _) = Parser.parseExpr("1 && 2 || 3")
    assert(op1 == BinaryOperator.LogicalOr)

    val IntegerExpression(_, r1Val) = r1
    assert(r1Val == 3)

    val BinaryExpression(l2, op2, r2) = l1
    assert(op2 == BinaryOperator.LogicalAnd)
    val IntegerExpression(_, l2Val) = l2
    val IntegerExpression(_, r2Val) = r2
    assert(l2Val == 1)
    assert(r2Val == 2)
  }

  test("&& / == precedence") {
    val Success(BinaryExpression(l, op1, r), _) =
      Parser.parseExpr(("1 == 2 && 3 == 4"))

    assert(op1 == BinaryOperator.LogicalAnd)

    val BinaryExpression(IntegerExpression(_, ll), opL, IntegerExpression(_, lr)) = l
    assert(opL == BinaryOperator.Equal)
    assert(ll == 1)
    assert(lr == 2)
    
    val BinaryExpression(IntegerExpression(_, rl), opR, IntegerExpression(_, rr)) = r
    assert(opR == BinaryOperator.Equal)
    assert(rl == 3)
    assert(rr == 4)
  }

  test("+ operator is left-associative") {
    // 1 + 2 + 3 should be the same as (1 + 2) + 3
    val Success(BinaryExpression(l, _, r), _) =
      Parser.parseExpr("1 + 2 + 3")
    
    val BinaryExpression(IntegerExpression(_, llValue), _, IntegerExpression(_, lrValue)) = l
    assert(llValue == 1)
    assert(lrValue == 2)

    val IntegerExpression(_, rValue) = r
    assert(rValue == 3)
  }

  test("+ / * precedence") {
    val Success(BinaryExpression(l, op, _), _) =
      Parser.parseExpr("1 * 2 + 3")
    assert(op == BinaryOperator.Add)

    val BinaryExpression(ll, opL, lr) = l
    assert(opL == BinaryOperator.Multiply)
  }

  test("method call") {
    val Success(InvokeExpression(Identifier(id), args), _) = Parser.parseExpr("test()")
    assert(id == "test")
    assert(args.isEmpty)
  }

  test("call with arg") {
    val Success(InvokeExpression(Identifier(id), args), _) = Parser.parseExpr("test(123)")
    assert(id == "test")

    val IntegerExpression(_, value) = args(0)
    assert(value == 123)
  }

  test("call with multiple args") {
    val Success(InvokeExpression(Identifier(id), args), _) = Parser.parseExpr("test(1, \"abc\")")
    assert(id == "test")

    val IntegerExpression(_, value1) = args(0)
    val StringExpression(_, value2) = args(1)
    assert(value1 == 1)
    assert(value2 == "abc")
  }

  test("dot member") {
    val Success(MemberExpression(parent, Identifier(fieldName), isArrow), _) = Parser.parseExpr("abc.def")
    assert(fieldName == "def")
    assert(!isArrow)

    val VariableExpression(Identifier(id)) = parent
    assert(id == "abc")
  }

  test("deref member") {
    val Success(MemberExpression(parent, Identifier(fieldName), isArrow), _) = Parser.parseExpr("abc->def")
    assert(fieldName == "def")
    assert(isArrow)

    val VariableExpression(Identifier(id)) = parent
    assert(id == "abc")
  }

  test("member of method call") {
    val Success(MemberExpression(parent, Identifier(fieldName), isArrow), _) = Parser.parseExpr("read().output")
    assert(fieldName == "output")
    assert(!isArrow)

    val InvokeExpression(Identifier(method), _) = parent
    assert(method == "read")
  }

  test("array index") {
    val Success(IndexExpression(parent, IntegerExpression(_, idx)), _) = Parser.parseExpr(("arr[0]"))
    assert(idx == 0)
    val VariableExpression(Identifier(id)) = parent
    assert(id == "arr")
  }

  test("unary not") {
    val Success(UnaryExpression(expr, op), _) = Parser.parseExpr("!test")
    assert(op == UnaryOperator.Not)
    val VariableExpression(Identifier(id)) = expr
    assert(id == "test")
  }

  test("repeated unary operators") {
    val Success(UnaryExpression(expr1, op1), _) = Parser.parseExpr("!!abc")
    assert(op1 == UnaryOperator.Not)
    val UnaryExpression(expr2, op2) = expr1
    assert(op2 == UnaryOperator.Not)
    val VariableExpression(Identifier(id)) = expr2
    assert(id == "abc")
  }
}