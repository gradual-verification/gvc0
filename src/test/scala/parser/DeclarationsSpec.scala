import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.Success

class DeclarationsSpec extends AnyFunSuite {
  test("struct declaration") {
    val Success(Seq(struct: StructDefinition), _) = Parser.parseDef("struct Test;")
    assert(struct.id == "Test")
    assert(struct.fields == None)
  }

  test("struct definition") {
    val Success(Seq(struct: StructDefinition), _) = Parser.parseDef("""
      struct Test {
        int field1;
        string field2;
      };
    """)

    assert(struct.id == "Test")
    val List(field1, field2) = struct.fields.get
    assert(field1.id == "field1")
    assert(field1.valueType.asInstanceOf[NamedType].id == "int")

    assert(field2.id == "field2")
    assert(field2.valueType.asInstanceOf[NamedType].id == "string")
  }

  test("type definition") {
    val Success(Seq(d: TypeDefinition), _) = Parser.parseDef("typedef int MyNumber;")
    assert(d.id == "MyNumber")
    assert(d.value.asInstanceOf[NamedType].id == "int")
  }

  test("typedef with struct type") {
    val Success(Seq(typeDef: TypeDefinition), _) = Parser.parseDef("typedef struct MyStruct MyStruct;")
    assert(typeDef.id == "MyStruct")
    assert(typeDef.value.asInstanceOf[NamedStructType].id == "MyStruct")
  }

  test("typedef with pointer") {
    val Success(Seq(typeDef: TypeDefinition), _) = Parser.parseDef("typedef int* NumberPointer;")
    assert(typeDef.id == "NumberPointer")
    assert(typeDef.value.asInstanceOf[PointerType].valueType.asInstanceOf[NamedType].id == "int")
  }

  test("method declaration") {
    val Success(Seq(method: MethodDefinition), _) = Parser.parseDef("int addOne(int value);")
    assert(method.id == "addOne")
    assert(method.returnType.asInstanceOf[NamedType].id == "int")

    val List(arg: MemberDefinition) = method.arguments
    assert(arg.id == "value")
    assert(arg.valueType.asInstanceOf[NamedType].id == "int")

    assert(method.body == None)
  }

  test("method declaration with precondition") {
    val Success(Seq(method: MethodDefinition), _) = Parser.parseDef("""
      int test(int a)
      /*@ requires(a > 0); @*/;
    """)

    assert(method.body == None)

    val List(spec: RequiresSpecification) = method.specifications
    val expr = spec.value.asInstanceOf[BinaryExpression]
    assert(expr.operator == BinaryOperator.Greater)
    assert(expr.left.asInstanceOf[VariableExpression].variable == "a")
    assert(expr.right.asInstanceOf[IntegerExpression] == 0)
  }

  test("method with multiple args") {
    val Success(Seq(method: MethodDefinition), _) = Parser.parseDef("int magnitude(int x, int y);")
    val List(arg1, arg2) = method.arguments
    assert(arg1.id == "x")
    assert(arg1.valueType.asInstanceOf[NamedType].id == "int")
    assert(arg2.id == "y")
    assert(arg2.valueType.asInstanceOf[NamedType].id == "int")
  }

  test("method with body") {
    val Success(Seq(method: MethodDefinition), _) = Parser.parseDef("""
      void test()
      {
        int a;
        a = 1;
        a++;
      }
    """)

    val List(stmt1, stmt2, stmt3) = method.body.get.body
    assert(stmt1.isInstanceOf[VariableStatement])
    assert(stmt2.isInstanceOf[AssignmentStatement])
    assert(stmt3.isInstanceOf[ExpressionStatement])
  }

  test("use library declaration") {
    val Success(Seq(use: UseDeclaration), _) = Parser.parseDef("#use <mylib>")
    assert(use.path.raw == "<mylib>")
    assert(use.path == "mylib")
    assert(use.isLibrary)
  }

  test("use path declaration") {
    val Success(Seq(use: UseDeclaration), _) = Parser.parseDef("#use \"test.c0\"")
    assert(use.path.raw == "\"test.c0\"")
    assert(use.path == "test.c0")
    assert(!use.isLibrary)
  }

  test("predicate definition") {
    val Success(Seq(pred: PredicateDefinition), _) = Parser.parseDef("//@ predicate test(int x) = x > 0;")
    assert(pred.id.name == "test")

    val List(arg: MemberDefinition) = pred.arguments
    assert(arg.id.name == "x")
    
    assert(pred.body.get.isInstanceOf[BinaryExpression])
  }

  test("multiple predicate definitions") {
    val Success(Seq(first: PredicateDefinition, second: PredicateDefinition), _) = Parser.parseDef("""
      /*@
        @predicate first() = true;
        predicate second(char c) = false;
      @*/
    """)

    assert(first.id.name == "first")
    assert(second.id.name === "second")
  }

  test("empty annotation") {
    assert(Parser.parseDef("//@ ").get.value.isEmpty)
    assert(Parser.parseDef("/*@  @*/").get.value.isEmpty)
  }
}