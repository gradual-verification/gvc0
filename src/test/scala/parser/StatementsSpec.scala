import fastparse.Parsed.{Success, Failure}
import org.scalatest.funsuite._
import gvc.parser._

class StatementsSpecExpr extends AnyFunSuite {
  test("literal statement") {
    val Success(stmt: ExpressionStatement, _) = Parser.parseStatement("123;")
    assert(stmt.expression.asInstanceOf[IntegerExpression] == 123)
  }

  test("invoke statement") {
    val Success(stmt: ExpressionStatement, _) = Parser.parseStatement("test(abc);")
    val invoke = stmt.expression.asInstanceOf[InvokeExpression]
    assert(invoke.method == "test")

    val List(arg: VariableExpression) = invoke.arguments
    assert(arg.variable == "abc")
  }

  test("assign var") {
    val Success(stmt: AssignmentStatement, _) = Parser.parseStatement("abc = 123;")
    assert(stmt.operator == AssignOperator.Assign)
    assert(stmt.left.asInstanceOf[VariableExpression].variable == "abc")
    assert(stmt.right.asInstanceOf[IntegerExpression] == 123)
  }

  test("assign dotted member") {
    val Success(stmt: AssignmentStatement, _) = Parser.parseStatement("abc.def = 123;")
    assert(stmt.operator == AssignOperator.Assign)

    val member = stmt.left.asInstanceOf[MemberExpression]
    assert(member.parent.asInstanceOf[VariableExpression].variable == "abc")
    assert(member.field == "def")
    assert(!member.isArrow)
  }

  test("add assign operator") {
    val Success(stmt: AssignmentStatement, _) = Parser.parseStatement("abc += 1;")
    assert(stmt.operator == AssignOperator.Add)
    assert(stmt.left.asInstanceOf[VariableExpression].variable == "abc")
  }

  test("assign member of pointer") {
    val Success(stmt: AssignmentStatement, _) = Parser.parseStatement("abc->def = 123;")
    val member = stmt.left.asInstanceOf[MemberExpression]
    assert(stmt.operator == AssignOperator.Assign)
    assert(member.parent.asInstanceOf[VariableExpression].variable == "abc")
    assert(member.field == "def")
    assert(member.isArrow)
  }

  test("assign array index") {
    val Success(stmt: AssignmentStatement, _) = Parser.parseStatement("abc[0] = 123;")
    val index = stmt.left.asInstanceOf[IndexExpression]
    assert(stmt.operator == AssignOperator.Assign)
    assert(index.parent.asInstanceOf[VariableExpression].variable == "abc")
    assert(index.index.asInstanceOf[IntegerExpression] == 0)
  }
  
  test("increment statement") {
    val Success(stmt: ExpressionStatement, _) = Parser.parseStatement("abc++;")
    val expr = stmt.expression.asInstanceOf[IncrementExpression]
    assert(expr.operator == IncrementOperator.Increment)
    assert(expr.value.asInstanceOf[VariableExpression].variable == "abc")
  }

  test("no prefix increment") {
    val Failure(_, _, _) = Parser.parseStatement("++abc;")
  }

  test("variable declaration") {
    val Success(stmt: VariableStatement, _) = Parser.parseStatement("int abc = 123;")
    assert(stmt.valueType.asInstanceOf[NamedType].id == "int")
    assert(stmt.id == "abc")
    assert(stmt.initialValue.get.asInstanceOf[IntegerExpression] == 123)
  }

  test("pointer variable") {
    val Success(stmt: VariableStatement, _) = Parser.parseStatement("search_tree* tree;")
    val baseType = stmt.valueType.asInstanceOf[PointerType].valueType
    assert(baseType.asInstanceOf[NamedType].id == "search_tree")
  }

  test("double pointer variable") {
    val Success(stmt: VariableStatement, _) = Parser.parseStatement("int** value;")
    val baseType = stmt.valueType.asInstanceOf[PointerType].valueType.asInstanceOf[PointerType].valueType
    assert(baseType.asInstanceOf[NamedType].id == "int")
  }

  test("struct variable") {
    val Success(stmt: VariableStatement, _) = Parser.parseStatement("struct node n;")
    assert(stmt.valueType.asInstanceOf[NamedStructType].id == "node");
  }

  test("variables with named types prefixed with struct") {
    val Success(stmt: VariableStatement, _) = Parser.parseStatement("structTest n;")
    assert(stmt.valueType.asInstanceOf[NamedType].id == "structTest");
  }

  test("empty block statement") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("{ }")
    assert(b.body == List.empty)
  }

  test("empty block with annotations") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("{ /*@ assert true; @*/ }")
    assert(b.body.isEmpty)

    val List(spec) = b.trailingSpecExprifications
    assert(spec.asInstanceOf[AssertSpecExprification].value.asInstanceOf[BooleanExpression] == true)
  }

  test("single statement block") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("{ a = 123; }")
    val List(stmt: AssignmentStatement) = b.body
    assert(stmt.left.asInstanceOf[VariableExpression].variable == "a")
    assert(stmt.right.asInstanceOf[IntegerExpression] == 123)
  }

  test("single statement block with annotations") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("""
      {
        /*@ assert false; @*/
        a = 123;
      }
    """)
    assert(b.specifications.isEmpty)
    assert(b.trailingSpecExprifications.isEmpty)

    val List(assign: AssignmentStatement) = b.body
    assert(assign.left.asInstanceOf[VariableExpression].variable == "a")
    assert(assign.operator == AssignOperator.Assign)
    assert(assign.right.asInstanceOf[IntegerExpression] == 123)

    val List(spec) = assign.specifications
    assert(spec.asInstanceOf[AssertSpecExprification].value.asInstanceOf[BooleanExpression] == false)
  }

  test("multi-statement block") {
    val Success(b: BlockStatement, _) = Parser.parseStatement("""
      {
        int a = 123;
        b = true ? "this" : "that";
        return 0;
      }
    """)

    val List(v: VariableStatement, a: AssignmentStatement, r: ReturnStatement) = b.body
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
    assert(stmt.ifTrue.asInstanceOf[AssignmentStatement].operator == AssignOperator.Assign)
    assert(stmt.ifFalse == None)
  }

  test("if block") {
    val Success(stmt: IfStatement, _) = Parser.parseStatement("if (false) { }")
    assert(stmt.ifTrue.asInstanceOf[BlockStatement].body.isEmpty)
    assert(stmt.ifFalse == None)
  }

  test("if else") {
    val Success(stmt: IfStatement, _) = Parser.parseStatement("""
      if (true)
        a = 2;
      else
        a = 3;
    """)

    val thenStmt = stmt.ifTrue.asInstanceOf[AssignmentStatement]
    assert(thenStmt.operator == AssignOperator.Assign)
    assert(thenStmt.right.asInstanceOf[IntegerExpression] == 2)

    val elseStmt = stmt.ifFalse.get.asInstanceOf[AssignmentStatement]
    assert(elseStmt.operator == AssignOperator.Assign)
    assert(elseStmt.right.asInstanceOf[IntegerExpression] == 3)
  }

  test("if else chain") {
    val Success(if1: IfStatement, _) = Parser.parseStatement("""
      if (a == 1) {
        doA();
      } else if (a == 2) {
        a++;
      } else {
        b++;
      }
    """)

    assert(if1.condition.asInstanceOf[BinaryExpression].right.asInstanceOf[IntegerExpression] == 1)
    assert(if1.ifTrue.asInstanceOf[BlockStatement].body.length == 1)
    
    val Some(if2: IfStatement) = if1.ifFalse
    assert(if2.condition.asInstanceOf[BinaryExpression].right.asInstanceOf[IntegerExpression] == 2)
    assert(if2.ifTrue.asInstanceOf[BlockStatement].body.length == 1)
    assert(if2.ifFalse.get.asInstanceOf[BlockStatement].body.length == 1)
  }

  test("while") {
    val Success(stmt: WhileStatement, _) = Parser.parseStatement("while (true) a += 2;")
    assert(stmt.condition.asInstanceOf[BooleanExpression] == true)
    val assign = stmt.body.asInstanceOf[AssignmentStatement]
    assert(assign.left.asInstanceOf[VariableExpression].variable == "a")
    assert(assign.operator == AssignOperator.Add)
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

    val inc = f.incrementor.asInstanceOf[ExpressionStatement].expression.asInstanceOf[IncrementExpression]
    assert(inc.operator == IncrementOperator.Increment)
    assert(inc.value.asInstanceOf[VariableExpression].variable == "i")

    val invoke = f.body.asInstanceOf[ExpressionStatement].expression.asInstanceOf[InvokeExpression]
    assert(invoke.method == "doSomething")
    assert(invoke.arguments == List.empty)
  }

  test("return") {
    val Success(stmt: ReturnStatement, _) = Parser.parseStatement("return;")
    assert(stmt.value == None)
  }

  test("return value") {
    val Success(stmt: ReturnStatement, _) = Parser.parseStatement("return 123;")
    assert(stmt.value.get.asInstanceOf[IntegerExpression] == 123)
  }

  test("require separator between return and value") {
    val Success(stmt: ExpressionStatement, _) = Parser.parseStatement("returntrue;")
    val variable = stmt.expression.asInstanceOf[VariableExpression]
    assert(variable.variable == "returntrue")
  }

  test("assert") {
    val Success(stmt: AssertStatement, _) = Parser.parseStatement("assert(true);")
    assert(stmt.value.asInstanceOf[BooleanExpression] == true)
  }

  test("error") {
    val Success(stmt: ErrorStatement, _) = Parser.parseStatement("error(\"test error\");")
    assert(stmt.value.asInstanceOf[StringExpression] == "test error")
  }

  
}