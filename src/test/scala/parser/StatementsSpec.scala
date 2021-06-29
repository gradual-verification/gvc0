import fastparse.Parsed.{Success, Failure}
import org.scalatest.funsuite._
import gvc.parser._

class StatementsSpec extends AnyFunSuite {
  test("literal statement") {
    val Success(ExpressionStatement(expr, _), _) = Parser.parseStatement("123;")
    assert(expr.asInstanceOf[IntegerExpression] == 123)
  }

  test("invoke statement") {
    val Success(ExpressionStatement(expr, _), _) = Parser.parseStatement("test(abc);")
    val InvokeExpression(id, args) = expr
    assert(id == "test")

    val VariableExpression(argId) = args(0)
    assert(argId == "abc")
  }

  test("assign var") {
    val Success(AssignmentStatement(lhs, op, rhs, _), _) = Parser.parseStatement("abc = 123;")
    assert(op == AssignOperator.Assign)
    assert(lhs.asInstanceOf[VariableExpression].variable == "abc")
    assert(rhs.asInstanceOf[IntegerExpression] == 123)
  }

  test("assign dotted member") {
    val Success(AssignmentStatement(lhs, op, _, _), _) = Parser.parseStatement("abc.def = 123;")
    assert(op == AssignOperator.Assign)
    val MemberExpression(VariableExpression(varId), fieldId, isArrow) = lhs
    assert(varId == "abc")
    assert(fieldId == "def")
    assert(!isArrow)
  }

  test("add assign operator") {
    val Success(AssignmentStatement(VariableExpression(id), op, _, _), _) = Parser.parseStatement("abc += 1;")
    assert(op == AssignOperator.Add)
    assert(id == "abc")
  }

  test("assign member of pointer") {
    val Success(AssignmentStatement(lhs, AssignOperator.Assign, _, _), _) = Parser.parseStatement("abc->def = 123;")
    val MemberExpression(VariableExpression(varId), fieldId, isArrow) = lhs
    assert(varId == "abc")
    assert(fieldId == "def")
    assert(isArrow)
  }

  test("assign array index") {
    val Success(AssignmentStatement(lhs, AssignOperator.Assign, _, _), _) = Parser.parseStatement("abc[0] = 123;")
    val IndexExpression(VariableExpression(varId), idx: IntegerExpression) = lhs
    assert(varId == "abc")
    assert(idx == 0)
  }
  
  test("increment statement") {
    val Success(UnaryOperationStatement(expr, op, _), _) = Parser.parseStatement("abc++;")
    assert(op == UnaryOperator.Increment)
    val VariableExpression(id) = expr
    assert(id == "abc")
  }

  test("no prefix increment") {
    val Failure(_, _, _) = Parser.parseStatement("++abc")
  }

  test("variable declaration") {
    val Success(VariableStatement(typ, id, value, _), _) = Parser.parseStatement("int abc = 123;")
    val NamedType(typeId) = typ
    assert(typeId == "int")
    assert(id == "abc")
    assert(value.get.asInstanceOf[IntegerExpression] == 123)
  }

  test("pointer variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("search_tree* tree;")
    val PointerType(NamedType(id)) = typ
    assert(id == "search_tree")
  }

  test("double pointer variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("int** value;")
    val PointerType(PointerType(NamedType(id))) = typ
    assert(id == "int")
  }

  test("struct variable") {
    val Success(VariableStatement(typ, _, _, _), _) = Parser.parseStatement("struct node n;")
    val NamedStructType(id) = typ
    assert(id == "node");
  }

  test("variables with named types prefixed with struct") {
    val Success(v: VariableStatement, _) = Parser.parseStatement("structTest n;")
    val NamedType(id) = v.valueType
    assert(id == "structTest");
  }

  test("empty block statement") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("{ }")
    assert(b.body == List.empty)
  }

  test("empty block with annotations") {
    val Success(BlockStatement(body, _, post), _) =
      Parser.parseStatement("{ /*@ assert true; @*/ }")
    assert(body == List())

    val List(spec) = post
    assert(spec.asInstanceOf[AssertSpecification].value.asInstanceOf[BooleanExpression] == true)
  }

  test("single statement block") {
    val Success(BlockStatement(body, _, _), _) = Parser.parseStatement("{ a = 123; }")
    assert(body.length == 1)
    val AssignmentStatement(VariableExpression(id), AssignOperator.Assign, value: IntegerExpression, _) = body(0)
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

    val List(assign: AssignmentStatement) = body
    assert(assign.left.asInstanceOf[VariableExpression].variable == "a")
    assert(assign.operator == AssignOperator.Assign)
    assert(assign.right.asInstanceOf[IntegerExpression] == 123)

    val List(spec) = assign.specifications
    assert(spec.asInstanceOf[AssertSpecification].value.asInstanceOf[BooleanExpression] == false)
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

    val List(v: VariableStatement, a: AssignmentStatement, r: ReturnStatement) = body
    assert(v.valueType.asInstanceOf[NamedType].id == "int")
    assert(v.id == "a")
    assert(v.initialValue.get.asInstanceOf[IntegerExpression] == 123)

    assert(a.left.asInstanceOf[VariableExpression].variable == "b")
    assert(a.operator == AssignOperator.Assign)
    assert(a.right.isInstanceOf[TernaryExpression])

    assert(r.value.get.asInstanceOf[IntegerExpression] == 0)
  }

  test("if") {
    val Success(stmt: IfStatement, _) = Parser.parseStatement("if (true) a = 2;")
    assert(stmt.condition.asInstanceOf[BooleanExpression] == true)
    assert(stmt.then.asInstanceOf[AssignmentStatement].operator == AssignOperator.Assign)
    assert(stmt.els == None)
  }

  test("if block") {
    val Success(IfStatement(_, body, None, _), _) = Parser.parseStatement("if (false) { }")
    val BlockStatement(statements, _, _) = body
    assert(statements == List.empty)
  }

  test("if else") {
    val Success(stmt: IfStatement, _) = Parser.parseStatement("""
      if (true)
        a = 2;
      else
        a = 3;
    """)

    val thenStmt = stmt.then.asInstanceOf[AssignmentStatement]
    assert(thenStmt.operator == AssignOperator.Assign)
    assert(thenStmt.right.asInstanceOf[IntegerExpression] == 2)

    val elseStmt = stmt.els.get.asInstanceOf[AssignmentStatement]
    assert(elseStmt.operator == AssignOperator.Assign)
    assert(elseStmt.right.asInstanceOf[IntegerExpression] == 3)
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
    val BinaryExpression(_, _, value1: IntegerExpression) = cond1
    val BlockStatement(statements1, _, _) = body1
    assert(value1 == 1)
    assert(statements1.length == 1)

    val Some(IfStatement(cond2, body2, else2, _)) = else1
    val BinaryExpression(_, _, value2: IntegerExpression) = cond2
    val BlockStatement(statements2, _, _) = body2
    assert(value2 == 2)
    assert(statements2.length == 1)

    val Some(BlockStatement(statements3, _, _)) = else2
    assert(statements3.length == 1)
  }

  test("while") {
    val Success(WhileStatement(cond, body, _), _) = Parser.parseStatement("while (true) a += 2;")
    assert(cond.asInstanceOf[BooleanExpression] == true)
    val AssignmentStatement(VariableExpression(id), op, _, _) = body
    assert(id == "a")
    assert(op == AssignOperator.Add)
  }

  test("for") {
    val Success(f: ForStatement, _) = Parser.parseStatement("for (int i = 0; i < 1; i++) doSomething();")
    
    val decl = f.initializer.asInstanceOf[VariableStatement]
    assert(decl.valueType.asInstanceOf[NamedType].id == "int")
    assert(decl.id == "i")
    assert(decl.initialValue.get.asInstanceOf[IntegerExpression] == 0)

    val cond = f.condition.asInstanceOf[BinaryExpression]
    assert(cond.left.asInstanceOf[VariableExpression].variable == "i")
    assert(cond.operator == BinaryOperator.Less)
    assert(cond.right.asInstanceOf[IntegerExpression] == 1)

    val inc = f.incrementor.asInstanceOf[UnaryOperationStatement]
    assert(inc.operator == UnaryOperator.Increment)
    assert(inc.value.asInstanceOf[VariableExpression].variable == "i")

    val invoke = f.body.asInstanceOf[ExpressionStatement].expression.asInstanceOf[InvokeExpression]
    assert(invoke.method == "doSomething")
    assert(invoke.arguments == List.empty)
  }

  test("return") {
    val Success(ReturnStatement(None, _), _) = Parser.parseStatement("return;")
  }

  test("return value") {
    val Success(ReturnStatement(Some(value), _), _) = Parser.parseStatement("return 123;")
    assert(value.asInstanceOf[IntegerExpression] == 123)
  }

  test("require separator between return and value") {
    val Success(ExpressionStatement(VariableExpression(name), _), _) = Parser.parseStatement("returntrue;")
    assert(name == "returntrue")
  }

  test("assert") {
    val Success(AssertStatement(value, _), _) = Parser.parseStatement("assert(true);")
    assert(value.asInstanceOf[BooleanExpression] == true)
  }

  test("error") {
    val Success(ErrorStatement(value, _), _) = Parser.parseStatement("error(\"test error\");")
    assert(value.asInstanceOf[StringExpression] == "test error")
  }

  
}