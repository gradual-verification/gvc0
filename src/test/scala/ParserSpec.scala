import org.scalatest.funsuite._
import gvc._
import fastparse.Parsed.{Success, Failure}

class ParserSpec extends AnyFunSuite {

  test("Parse variable") {
    val Success(VariableExpression("abc"), _) = Parser.parseExpr("abc")
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
    val Success(VariableExpression("True"), _) = Parser.parseExpr("True")
    val Success(VariableExpression("TRUE"), _) = Parser.parseExpr("TRUE")
    val Success(VariableExpression("False"), _) = Parser.parseExpr("False")
    val Success(VariableExpression("FALSE"), _) = Parser.parseExpr("FALSE")
  }

  test("NULL literal") {
    val Success(NullExpression("NULL", null), _) = Parser.parseExpr("NULL")
  }

  test("Null with difference case is variable") {
    val Success(VariableExpression("Null"), _) = Parser.parseExpr("Null")
    val Success(VariableExpression("null"), _) = Parser.parseExpr("null")
  }

  test("alloc expression") {
    val Success(AllocExpression(NamedType("Test")), _) = Parser.parseExpr("alloc(Test)")
  }

  test("alloc_array expression") {
    val Success(AllocArrayExpression(NamedType("Test"), IntegerExpression("10", 10)), _) =
      Parser.parseExpr("alloc_array(Test, 10)")
  }

  test("ternary expression") {
    val Success(TernaryOperation(BooleanExpression("true", true), IntegerExpression("1", 1), IntegerExpression("2", 2)), _) =
      Parser.parseExpr("true ? 1 : 2")
  }

  test("nested ternaries") {
    val Success(
      TernaryOperation(
        BooleanExpression("false", false),
        IntegerExpression("1", 1),
        TernaryOperation(
          BooleanExpression("true", true),
          IntegerExpression("2", 2),
          IntegerExpression("3", 3)
        )
      ), _
    ) = Parser.parseExpr("false ? 1 : true ? 2 : 3")

    val Success(
      TernaryOperation(
        BooleanExpression("false", false),
        TernaryOperation(
          BooleanExpression("true", true),
          IntegerExpression("1", 1),
          IntegerExpression("2", 2)
        ),
        IntegerExpression("3", 3),
      ), _
    ) = Parser.parseExpr("false ? true ? 1 : 2 : 3")
  }

  test("&&") {
    val Success(BinaryExpression(BooleanExpression(_, true), BooleanExpression(_, false), op), _) =
      Parser.parseExpr("true && false")
    assert(op == BinaryOp.LogicalAnd)
  }

  test("||") {
    val Success(BinaryExpression(BooleanExpression(_, true), BooleanExpression(_, false), op), _) =
      Parser.parseExpr("true || false")
    assert(op == BinaryOp.LogicalOr)
  }

  test ("&& / || precedence") {
    val Success(BinaryExpression(l1, r1, op1), _) = Parser.parseExpr("1 && 2 || 3")
    assert(op1 == BinaryOp.LogicalOr)

    val IntegerExpression(_, r1Val) = r1
    assert(r1Val == 3)

    val BinaryExpression(l2, r2, op2) = l1
    assert(op2 == BinaryOp.LogicalAnd)
    val IntegerExpression(_, l2Val) = l2
    val IntegerExpression(_, r2Val) = r2
    assert(l2Val == 1)
    assert(r2Val == 2)
  }

  test("&& / == precedence") {
    val Success(BinaryExpression(l, r, op1), _) =
      Parser.parseExpr(("1 == 2 && 3 == 4"))

    assert(op1 == BinaryOp.LogicalAnd)

    val BinaryExpression(IntegerExpression(_, ll), IntegerExpression(_, lr), opL) = l
    assert(opL == BinaryOp.Equal)
    assert(ll == 1)
    assert(lr == 2)
    
    val BinaryExpression(IntegerExpression(_, rl), IntegerExpression(_, rr), opR) = r
    assert(opR == BinaryOp.Equal)
    assert(rl == 3)
    assert(rr == 4)
  }

  test("+ operator is left-associative") {
    // 1 + 2 + 3 should be the same as (1 + 2) + 3
    val Success(BinaryExpression(l, r, _), _) =
      Parser.parseExpr("1 + 2 + 3")
    
    assert(l.isInstanceOf[BinaryExpression])
    val BinaryExpression(IntegerExpression(_, llValue), IntegerExpression(_, lrValue), _) = l
    assert(llValue == 1)
    assert(lrValue == 2)

    assert(r.isInstanceOf[IntegerExpression])
    val IntegerExpression(_, rValue) = r
    assert(rValue == 3)
  }

  test("+ / * precedence") {
    val Success(BinaryExpression(l, _, op), _) =
      Parser.parseExpr("1 * 2 + 3")
    assert(op == BinaryOp.Add)

    val BinaryExpression(ll, lr, opL) = l
    assert(opL == BinaryOp.Multiply)
  }

  test("method call") {
    val Success(InvokeExpression(id, args), _) = Parser.parseExpr("test()")
    assert(id == "test")
    assert(args.isEmpty)
  }

  test("call with arg") {
    val Success(InvokeExpression(id, args), _) = Parser.parseExpr("test(123)")
    assert(id == "test")

    val IntegerExpression(_, value) = args(0)
    assert(value == 123)
  }

  test("call with multiple args") {
    val Success(InvokeExpression(id, args), _) = Parser.parseExpr("test(1, \"abc\")")
    assert(id == "test")

    val IntegerExpression(_, value1) = args(0)
    val StringExpression(_, value2) = args(1)
    assert(value1 == 1)
    assert(value2 == "abc")
  }

  test("dot member") {
    val Success(MemberExpression(parent, field), _) = Parser.parseExpr("abc.def")
    assert(field == "def")

    val VariableExpression(id) = parent
    assert(id == "abc")
  }

  test("deref member") {
    val Success(MemberDerefExpression(parent, field), _) = Parser.parseExpr("abc->def")
    assert(field == "def")
    val VariableExpression(id) = parent
    assert(id == "abc")
  }

  test("member of method call") {
    val Success(MemberExpression(parent, field), _) = Parser.parseExpr("read().output")
    assert(field == "output")
    val InvokeExpression(method, _) = parent
    assert(method == "read")
  }

  test("array index") {
    val Success(IndexExpression(parent, IntegerExpression(_, idx)), _) = Parser.parseExpr(("arr[0]"))
    assert(idx == 0)
    val VariableExpression(id) = parent
    assert(id == "arr")
  }

  test("unary not") {
    val Success(UnaryExpression(expr, op), _) = Parser.parseExpr("!test")
    assert(op == UnaryOp.Not)
    val VariableExpression(id) = expr
    assert(id == "test")
  }

  test("repeated unary operators") {
    val Success(UnaryExpression(expr1, op1), _) = Parser.parseExpr("!!abc")
    assert(op1 == UnaryOp.Not)
    val UnaryExpression(expr2, op2) = expr1
    assert(op2 == UnaryOp.Not)
    val VariableExpression(id) = expr2
    assert(id == "abc")
  }

  test("literal statement") {
    val Success(ExpressionStatement(expr), _) = Parser.parseStatement("123;")
    val IntegerExpression(_, value) = expr
    assert(value == 123)
  }

  test("invoke statement") {
    val Success(ExpressionStatement(expr), _) = Parser.parseStatement("test(abc);")
    val InvokeExpression(id, args) = expr
    assert(id == "test")

    val VariableExpression(argId) = args(0)
    assert(argId == "abc")
  }

  test("assign var") {
    val Success(AssignmentStatement(lhs, op, rhs), _) = Parser.parseStatement("abc = 123;")
    assert(op == AssignOp.Assign)
    
    val VariableExpression(id) = lhs
    assert(id == "abc")

    val IntegerExpression(_, value) = rhs
    assert(value == 123)
  }

  test("assign dotted member") {
    val Success(AssignmentStatement(lhs, op, _), _) = Parser.parseStatement("abc.def = 123;")
    assert(op == AssignOp.Assign)
    val MemberExpression(VariableExpression(varId), field) = lhs
    assert(varId == "abc")
    assert(field == "def")
  }

  test("add assign operator") {
    val Success(AssignmentStatement(VariableExpression(id), op, _), _) = Parser.parseStatement("abc += 1;")
    assert(op == AssignOp.Add)
    assert(id == "abc")
  }

  test("assign member of pointer") {
    val Success(AssignmentStatement(lhs, AssignOp.Assign, _), _) = Parser.parseStatement("abc->def = 123;")
    val MemberDerefExpression(VariableExpression(varId), field) = lhs
    assert(varId == "abc")
    assert(field == "def")
  }

  test("assign array index") {
    val Success(AssignmentStatement(lhs, AssignOp.Assign, _), _) = Parser.parseStatement("abc[0] = 123;")
    val IndexExpression(VariableExpression(varId), idx) = lhs
    assert(varId == "abc")
    
    val IntegerExpression(_, idxValue) = idx
    assert(idxValue == 0)
  }
  
  test("increment statement") {
    val Success(UnaryOperationStatement(expr, op), _) = Parser.parseStatement("abc++;")
    assert(op == UnaryOp.Increment)
    val VariableExpression(id) = expr
    assert(id == "abc")
  }

  test("no prefix increment") {
    val Failure(_, _, _) = Parser.parseStatement("++abc")
  }

  test("variable declaration") {
    val Success(VariableStatement(typ, id, value), _) = Parser.parseStatement("int abc = 123;")
    val NamedType(typeId) = typ
    assert(typeId == "int")
    assert(id == "abc")

    val Some(IntegerExpression(_, intValue)) = value
    assert(intValue == 123)
  }

  test("empty block statement") {
    val Success(BlockStatement(body), _) = Parser.parseStatement("{ }")
    assert(body == List.empty)
  }

  test("single statement block") {
    val Success(BlockStatement(body), _) = Parser.parseStatement("{ a = 123; }")
    assert(body.length == 1)
    val AssignmentStatement(VariableExpression(id), AssignOp.Assign, IntegerExpression(_, value)) = body(0)
    assert(id == "a")
    assert(value == 123)
  }

  test("multi-statement block") {
    val Success(BlockStatement(body), _) = Parser.parseStatement("""
      {
        int a = 123;
        b = true ? "this" : "that";
        return 0;
      }
    """)

    assert(body.length == 3)
    val VariableStatement(NamedType(aType), aVar, Some(IntegerExpression(_, aValue))) = body(0)
    assert(aType == "int")
    assert(aVar == "a")
    assert(aValue == 123)

    val AssignmentStatement(VariableExpression(bVar), AssignOp.Assign, TernaryOperation(_, _, _)) = body(1)
    assert(bVar == "b")

    val ReturnStatement(Some(IntegerExpression(_, retValue))) = body(2)
    assert(retValue == 0)
  }

  test("if") {
    val Success(IfStatement(cond, body, els), _) = Parser.parseStatement("if (true) a = 2;")
    val BooleanExpression(_, condValue) = cond
    assert(condValue == true)
    val AssignmentStatement(_, AssignOp.Assign, _) = body
    assert(els == None)
  }

  test("if block") {
    val Success(IfStatement(_, body, None), _) = Parser.parseStatement("if (false) { }")
    val BlockStatement(statements) = body
    assert(statements == List.empty)
  }

  test("if else") {
    val Success(IfStatement(_, body, els), _) = Parser.parseStatement("""
      if (true)
        a = 2;
      else
        a = 3;
    """)
    val AssignmentStatement(_, AssignOp.Assign, ifTrue) = body
    val IntegerExpression(_, ifTrueValue) = ifTrue
    assert(ifTrueValue == 2)

    val Some(elseStmt) = els
    val AssignmentStatement(_, AssignOp.Assign, ifFalse) = elseStmt
    val IntegerExpression(_, ifFalseValue) = ifFalse
    assert(ifFalseValue == 3)
  }

  test("if else chain") {
    val Success(if1, _) = Parser.parseStatement("""
      if (a == 1) {
        doA();
      } else if (a == 2) {
        a++;
      } else {
        b++;
      }
    """)

    val IfStatement(cond1, body1, else1) = if1
    val BinaryExpression(_, IntegerExpression(_, value1), _) = cond1
    val BlockStatement(statements1) = body1
    assert(value1 == 1)
    assert(statements1.length == 1)

    val Some(IfStatement(cond2, body2, else2)) = else1
    val BinaryExpression(_, IntegerExpression(_, value2), _) = cond2
    val BlockStatement(statements2) = body2
    assert(value2 == 2)
    assert(statements2.length == 1)

    val Some(BlockStatement(statements3)) = else2
    assert(statements3.length == 1)
  }

  test("while") {
    val Success(WhileStatement(cond, body), _) = Parser.parseStatement("while (true) a += 2;")
    val BooleanExpression(_, true) = cond
    val AssignmentStatement(VariableExpression(id), op, _) = body
    assert(id == "a")
    assert(op == AssignOp.Add)
  }

  test("for") {
    val Success(ForStatement(decl, cond, inc, body), _) =
      Parser.parseStatement("for (int i = 0; i < 1; i++) doSomething();")
    
    val VariableStatement(NamedType(iType), iId, iInitial) = decl
    assert(iType == "int")
    assert(iId == "i")
    val Some(IntegerExpression(_, iValue)) = iInitial
    assert(iValue == 0)

    val BinaryExpression(iRef, compare, op) = cond
    val VariableExpression("i") = iRef
    val IntegerExpression(_, 1) = compare
    assert(op == BinaryOp.Less)

    val UnaryOperationStatement(iRef2, UnaryOp.Increment) = inc
    val VariableExpression("i") = iRef2

    val ExpressionStatement(InvokeExpression(id, args)) = body
    assert(id == "doSomething")
    assert(args == List.empty)
  }

  test("return") {
    val Success(ReturnStatement(None), _) = Parser.parseStatement("return;")
  }

  test("return value") {
    val Success(ReturnStatement(Some(value)), _) = Parser.parseStatement("return 123;")
    val IntegerExpression(_, intValue) = value
    assert(intValue == 123)
  }

  test("assert") {
    val Success(AssertStatement(value), _) = Parser.parseStatement("assert(true);")
    val BooleanExpression(_, bool) = value
    assert(bool == true)
  }

  test("error") {
    val Success(ErrorStatement(value), _) = Parser.parseStatement("error(\"test error\");")
    val StringExpression(_, str) = value
    assert(str == "test error")
  }

  test("struct declaration") {
    val Success(StructDefinition(name, fields), _) = Parser.parseDef("struct Test;")
    assert(name == "Test")
    assert(fields == None)
  }

  test("struct definition") {
    val Success(StructDefinition(name, Some(fields)), _) = Parser.parseDef("""
      struct Test {
        int field1;
        string field2;
      };
    """)

    assert(name == "Test")
    val List(field1, field2) = fields
    val MemberDefinition(name1, NamedType(type1)) = field1
    assert(name1 == "field1")
    assert(type1 == "int")

    val MemberDefinition(name2, NamedType(type2)) = field2
    assert(name2 == "field2")
    assert(type2 == "string")
  }

  test("type definition") {
    val Success(TypeDefinition(name, typ), _) = Parser.parseDef("typedef int MyNumber;")
    assert(name == "MyNumber")
    
    val NamedType(typeName) = typ
    assert(typeName == "int")
  }

  test("typedef with struct type") {
    val Success(TypeDefinition(name, structType), _) = Parser.parseDef("typedef struct MyStruct MyStruct;")
    assert(name == "MyStruct")

    val NamedStructType(structName) = structType
    assert(structName == "MyStruct")
  }

  test("typedef with pointer") {
    val Success(TypeDefinition(name, defType), _) = Parser.parseDef("typedef int* NumberPointer;")
    assert(name == "NumberPointer")

    val PointerType(NamedType(typeName)) = defType
    assert(typeName == "int")
  }

  test("method declaration") {
    val Success(method, _) = Parser.parseDef("int addOne(int value);")
    val MethodDefinition(name, retType, args, body) = method
    assert(name == "addOne")

    val NamedType(retTypeName) = retType
    assert(retTypeName == "int")

    val List(MemberDefinition(argName, NamedType(argType))) = args
    assert(argName == "value")
    assert(argType == "int")

    assert(body == None)
  }

  test("method with multiple args") {
    val Success(method, _) = Parser.parseDef("int magnitude(int x, int y);")
    val MethodDefinition(name, _, args, None) = method
    val List(
      MemberDefinition(name1, NamedType(type1)),
      MemberDefinition(name2, NamedType(type2))
    ) = args
    assert(name1 == "x")
    assert(type1 == "int")
    assert(name2 == "y")
    assert(type2 == "int")
  }

  test("method with body") {
    val Success(MethodDefinition(name, _, _, Some(body)), _) = Parser.parseDef("""
      void test()
      {
        int a;
        a = 1;
        a++;
      }
    """)

    val BlockStatement(List(stmt1, stmt2, stmt3)) = body
    assert(stmt1.isInstanceOf[VariableStatement])
    assert(stmt2.isInstanceOf[AssignmentStatement])
    assert(stmt3.isInstanceOf[UnaryOperationStatement])
  }

  test("use library declaration") {
    val Success(UseDeclaration(path, isLibrary), _) = Parser.parseDef("#use <mylib>")
    val StringExpression(raw, value) = path
    assert(raw == "<mylib>")
    assert(value == "mylib")
    assert(isLibrary)
  }

  test("use path declaration") {
    val Success(UseDeclaration(path, isLibrary), _) = Parser.parseDef("#use \"test.c0\"")
    val StringExpression(raw, value) = path
    assert(raw == "\"test.c0\"")
    assert(value == "test.c0")
    assert(!isLibrary)
  }

  test("empty program") {
    val Success(defs, _) = Parser.parseProgram("\n")
    assert(defs == List.empty)
  }

  test("isPrime example") {
    // Taken from https://bitbucket.org/c0-lang/docs/wiki/Computing_primes_in_Python_and_C0
    val Success(defs, _) = Parser.parseProgram("""
      bool isPrime(int n)
      {
        if (n < 2) return false;
        if (n == 2) return true;
        if (n % 2 == 0) return false;
        for (int factor = 3; factor <= n/factor; factor += 2) {
          if (n % factor == 0)
            return false;
        }
        return true;
      }
    """)

    val List(MethodDefinition(methodName, methodReturn, methodArgs, methodBody)) = defs
    assert(methodName == "isPrime")

    val List(MemberDefinition(argName, _)) = methodArgs
    assert(argName == "n")

    val Some(BlockStatement(statements)) = methodBody
    assert(statements.length == 5)
  }

  test("line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      // this is a test
      // another test
    """)
  }

  test("multi-line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      /*
        This is a comment
      */
    """)
  }

  test("nested multi-line comments") {
    val Success(List(), _) = Parser.parseProgram("""
      /*
        /* This is a comment */
      */
    """)
  }
}