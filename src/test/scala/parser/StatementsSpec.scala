import fastparse.Parsed.{Success, Failure}
import org.scalatest.funsuite._
import gvc.parser._

class StatementsSpec extends AnyFunSuite {
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

  test("pointer variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("search_tree* tree;")
    val PointerType(NamedType(Identifier(name))) = typ
    assert(name == "search_tree")
  }

  test("double pointer variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("int** value;")
    val PointerType(PointerType(NamedType(Identifier(name)))) = typ
    assert(name == "int")
  }

  test("struct variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("struct node n;")
    val NamedStructType(Identifier(name)) = typ
    assert(name == "node");
  }

  test("variables with named types prefixed with struct") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("structTest n;")
    val NamedType(Identifier(name)) = typ
    assert(name == "structTest");
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

  test("require separator between return and value") {
    val Success(ExpressionStatement(VariableExpression(Identifier(name)), _), _) = Parser.parseStatement("returntrue;")
    assert(name == "returntrue")
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

  
}