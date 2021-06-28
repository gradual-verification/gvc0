import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class ParserSpec extends AnyFunSuite {

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

  test("literal statement") {
    val Success(ExpressionStatement(expr, _), _) = Parser.parseStatement("123;")
    val IntegerExpression(_, value) = expr
    assert(value == 123)
  }

  test("invoke statement") {
    val Success(ExpressionStatement(expr, _), _) = Parser.parseStatement("test(abc);")
    val InvokeExpression(Identifier(id), args) = expr
    assert(id == "test")

    val VariableExpression(Identifier(argId)) = args(0)
    assert(argId == "abc")
  }

  test("assign var") {
    val Success(AssignmentStatement(lhs, op, rhs, _), _) = Parser.parseStatement("abc = 123;")
    assert(op == AssignOperator.Assign)
    
    val VariableExpression(Identifier(id)) = lhs
    assert(id == "abc")

    val IntegerExpression(_, value) = rhs
    assert(value == 123)
  }

  test("assign dotted member") {
    val Success(AssignmentStatement(lhs, op, _, _), _) = Parser.parseStatement("abc.def = 123;")
    assert(op == AssignOperator.Assign)
    val MemberExpression(VariableExpression(Identifier(varId)), Identifier(field), isArrow) = lhs
    assert(varId == "abc")
    assert(field == "def")
    assert(!isArrow)
  }

  test("add assign operator") {
    val Success(AssignmentStatement(VariableExpression(Identifier(id)), op, _, _), _) = Parser.parseStatement("abc += 1;")
    assert(op == AssignOperator.Add)
    assert(id == "abc")
  }

  test("assign member of pointer") {
    val Success(AssignmentStatement(lhs, AssignOperator.Assign, _, _), _) = Parser.parseStatement("abc->def = 123;")
    val MemberExpression(VariableExpression(Identifier(varId)), Identifier(field), isArrow) = lhs
    assert(varId == "abc")
    assert(field == "def")
    assert(isArrow)
  }

  test("assign array index") {
    val Success(AssignmentStatement(lhs, AssignOperator.Assign, _, _), _) = Parser.parseStatement("abc[0] = 123;")
    val IndexExpression(VariableExpression(Identifier(varId)), idx) = lhs
    assert(varId == "abc")
    
    val IntegerExpression(_, idxValue) = idx
    assert(idxValue == 0)
  }
  
  test("increment statement") {
    val Success(UnaryOperationStatement(expr, op, _), _) = Parser.parseStatement("abc++;")
    assert(op == UnaryOperator.Increment)
    val VariableExpression(Identifier(id)) = expr
    assert(id == "abc")
  }

  test("no prefix increment") {
    val Failure(_, _, _) = Parser.parseStatement("++abc")
  }

  test("variable declaration") {
    val Success(VariableStatement(typ, id, value, _), _) = Parser.parseStatement("int abc = 123;")
    val NamedType(Identifier(typeId)) = typ
    assert(typeId == "int")

    val Identifier(name) = id
    assert(name == "abc")

    val Some(IntegerExpression(_, intValue)) = value
    assert(intValue == 123)
  }

  test("empty block statement") {
    val Success(BlockStatement(body, _, _), _) = Parser.parseStatement("{ }")
    assert(body == List.empty)
  }

  test("empty block with annotations") {
    val Success(BlockStatement(body, _, post), _) =
      Parser.parseStatement("{ /*@ assert true; @*/ }")
    assert(body == List())

    val List(AssertSpecification(value)) = post
    val BooleanExpression(_, v) = value
    assert(v == true)
  }

  test("single statement block") {
    val Success(BlockStatement(body, _, _), _) = Parser.parseStatement("{ a = 123; }")
    assert(body.length == 1)
    val AssignmentStatement(VariableExpression(Identifier(id)), AssignOperator.Assign, IntegerExpression(_, value), _) = body(0)
    assert(id == "a")
    assert(value == 123)
  }

  test("single statement block with annotations") {
    val Success(BlockStatement(body, blockPre, blockPost), _) = Parser.parseStatement("""
      {
        /*@ assert false; @*/
        a = 123;
      }
    """)
    assert(body.length == 1)
    assert(blockPre == List())
    assert(blockPost == List())

    val AssignmentStatement(VariableExpression(Identifier(id)), AssignOperator.Assign, IntegerExpression(_, value), specs) = body(0)
    assert(id == "a")
    assert(value == 123)

    val List(AssertSpecification(assertBool)) = specs
    val BooleanExpression(_, assertVal) = assertBool
    assert(assertVal == false)
  }

  test("multi-statement block") {
    val Success(BlockStatement(body, _, _), _) = Parser.parseStatement("""
      {
        int a = 123;
        b = true ? "this" : "that";
        return 0;
      }
    """)

    assert(body.length == 3)
    val VariableStatement(NamedType(Identifier(aType)), Identifier(aVar), Some(IntegerExpression(_, aValue)), _) = body(0)
    assert(aType == "int")
    assert(aVar == "a")
    assert(aValue == 123)

    val AssignmentStatement(VariableExpression(Identifier(bVar)), AssignOperator.Assign, TernaryExpression(_, _, _), _) = body(1)
    assert(bVar == "b")

    val ReturnStatement(Some(IntegerExpression(_, retValue)), _) = body(2)
    assert(retValue == 0)
  }

  test("if") {
    val Success(IfStatement(cond, body, els, _), _) = Parser.parseStatement("if (true) a = 2;")
    val BooleanExpression(_, condValue) = cond
    assert(condValue == true)
    val AssignmentStatement(_, AssignOperator.Assign, _, _) = body
    assert(els == None)
  }

  test("if block") {
    val Success(IfStatement(_, body, None, _), _) = Parser.parseStatement("if (false) { }")
    val BlockStatement(statements, _, _) = body
    assert(statements == List.empty)
  }

  test("if else") {
    val Success(IfStatement(_, body, els, _), _) = Parser.parseStatement("""
      if (true)
        a = 2;
      else
        a = 3;
    """)
    val AssignmentStatement(_, AssignOperator.Assign, ifTrue, _) = body
    val IntegerExpression(_, ifTrueValue) = ifTrue
    assert(ifTrueValue == 2)

    val Some(elseStmt) = els
    val AssignmentStatement(_, AssignOperator.Assign, ifFalse, _) = elseStmt
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

    val IfStatement(cond1, body1, else1, _) = if1
    val BinaryExpression(_, _, IntegerExpression(_, value1)) = cond1
    val BlockStatement(statements1, _, _) = body1
    assert(value1 == 1)
    assert(statements1.length == 1)

    val Some(IfStatement(cond2, body2, else2, _)) = else1
    val BinaryExpression(_, _, IntegerExpression(_, value2)) = cond2
    val BlockStatement(statements2, _, _) = body2
    assert(value2 == 2)
    assert(statements2.length == 1)

    val Some(BlockStatement(statements3, _, _)) = else2
    assert(statements3.length == 1)
  }

  test("while") {
    val Success(WhileStatement(cond, body, _), _) = Parser.parseStatement("while (true) a += 2;")
    val BooleanExpression(_, true) = cond
    val AssignmentStatement(VariableExpression(Identifier(id)), op, _, _) = body
    assert(id == "a")
    assert(op == AssignOperator.Add)
  }

  test("for") {
    val Success(ForStatement(decl, cond, inc, body, _), _) =
      Parser.parseStatement("for (int i = 0; i < 1; i++) doSomething();")
    
    val VariableStatement(NamedType(Identifier(iType)), Identifier(iId), iInitial, _) = decl
    assert(iType == "int")
    assert(iId == "i")
    val Some(IntegerExpression(_, iValue)) = iInitial
    assert(iValue == 0)

    val BinaryExpression(iRef, op, compare) = cond
    val VariableExpression(Identifier("i")) = iRef
    val IntegerExpression(_, 1) = compare
    assert(op == BinaryOperator.Less)

    val UnaryOperationStatement(iRef2, UnaryOperator.Increment, _) = inc
    val VariableExpression(Identifier("i")) = iRef2

    val ExpressionStatement(InvokeExpression(Identifier(id), args), _) = body
    assert(id == "doSomething")
    assert(args == List.empty)
  }

  test("return") {
    val Success(ReturnStatement(None, _), _) = Parser.parseStatement("return;")
  }

  test("return value") {
    val Success(ReturnStatement(Some(value), _), _) = Parser.parseStatement("return 123;")
    val IntegerExpression(_, intValue) = value
    assert(intValue == 123)
  }

  test("assert") {
    val Success(AssertStatement(value, _), _) = Parser.parseStatement("assert(true);")
    val BooleanExpression(_, bool) = value
    assert(bool == true)
  }

  test("error") {
    val Success(ErrorStatement(value, _), _) = Parser.parseStatement("error(\"test error\");")
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
    val MemberDefinition(name1, NamedType(Identifier(type1))) = field1
    assert(name1 == "field1")
    assert(type1 == "int")

    val MemberDefinition(name2, NamedType(Identifier(type2))) = field2
    assert(name2 == "field2")
    assert(type2 == "string")
  }

  test("type definition") {
    val Success(TypeDefinition(name, typ), _) = Parser.parseDef("typedef int MyNumber;")
    assert(name == "MyNumber")
    
    val NamedType(Identifier(typeName)) = typ
    assert(typeName == "int")
  }

  test("typedef with struct type") {
    val Success(TypeDefinition(name, structType), _) = Parser.parseDef("typedef struct MyStruct MyStruct;")
    assert(name == "MyStruct")

    val NamedStructType(Identifier(structName)) = structType
    assert(structName == "MyStruct")
  }

  test("typedef with pointer") {
    val Success(TypeDefinition(name, defType), _) = Parser.parseDef("typedef int* NumberPointer;")
    assert(name == "NumberPointer")

    val PointerType(NamedType(Identifier(typeName))) = defType
    assert(typeName == "int")
  }

  test("method declaration") {
    val Success(method, _) = Parser.parseDef("int addOne(int value);")
    val MethodDefinition(Identifier(name), retType, args, body, _) = method
    assert(name == "addOne")

    val NamedType(Identifier(retTypeName)) = retType
    assert(retTypeName == "int")

    val List(MemberDefinition(argName, NamedType(Identifier(argType)))) = args
    assert(argName == "value")
    assert(argType == "int")

    assert(body == None)
  }

  test("method declaration with precondition") {
    val Success(method, _) = Parser.parseDef("""
      int test(int a)
      /*@ requires(a > 0); @*/;
    """)

    val MethodDefinition(_, _, _, body, spec) = method
    assert(body == None)

    val List(RequiresSpecification(value)) = spec
    val BinaryExpression(l, op, r) = value
    assert(op == BinaryOperator.Greater)

    val VariableExpression(Identifier(id)) = l
    val IntegerExpression(_, i) = r
    assert(id == "a")
    assert(i == 0)
  }

  test("method with multiple args") {
    val Success(method, _) = Parser.parseDef("int magnitude(int x, int y);")
    val MethodDefinition(name, _, args, None, _) = method
    val List(
      MemberDefinition(name1, NamedType(Identifier(type1))),
      MemberDefinition(name2, NamedType(Identifier(type2)))
    ) = args
    assert(name1 == "x")
    assert(type1 == "int")
    assert(name2 == "y")
    assert(type2 == "int")
  }

  test("method with body") {
    val Success(MethodDefinition(name, _, _, Some(body), _), _) = Parser.parseDef("""
      void test()
      {
        int a;
        a = 1;
        a++;
      }
    """)

    val BlockStatement(List(stmt1, stmt2, stmt3), _, _) = body
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

    val List(MethodDefinition(Identifier(methodName), methodReturn, methodArgs, methodBody, _)) = defs
    assert(methodName == "isPrime")

    val List(MemberDefinition(argName, _)) = methodArgs
    assert(argName == "n")

    val Some(BlockStatement(statements, _, _)) = methodBody
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