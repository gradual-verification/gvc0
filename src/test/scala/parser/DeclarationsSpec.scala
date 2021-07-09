import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class DeclarationsSpec extends AnyFunSuite {
  test("struct declaration") {
    val Success(struct: StructDefinition, _) = Parser.parseDef("struct Test;")
    assert(struct.id == "Test")
    assert(struct.fields == None)
  }

  test("struct definition") {
    val Success(struct: StructDefinition, _) = Parser.parseDef("""
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
    val Success(d: TypeDefinition, _) = Parser.parseDef("typedef int MyNumber;")
    assert(d.id == "MyNumber")
    assert(d.value.asInstanceOf[NamedType].id == "int")
  }

  test("typedef with struct type") {
    val Success(typeDef: TypeDefinition, _) = Parser.parseDef("typedef struct MyStruct MyStruct;")
    assert(typeDef.id == "MyStruct")
    assert(typeDef.value.asInstanceOf[NamedStructType].id == "MyStruct")
  }

  test("typedef with pointer") {
    val Success(typeDef: TypeDefinition, _) = Parser.parseDef("typedef int* NumberPointer;")
    assert(typeDef.id == "NumberPointer")
    assert(typeDef.value.asInstanceOf[PointerType].valueType.asInstanceOf[NamedType].id == "int")
  }

  test("method declaration") {
    val Success(method: MethodDefinition, _) = Parser.parseDef("int addOne(int value);")
    assert(method.id == "addOne")
    assert(method.returnType.asInstanceOf[NamedType].id == "int")

    val List(arg: MemberDefinition) = method.arguments
    assert(arg.id == "value")
    assert(arg.valueType.asInstanceOf[NamedType].id == "int")

    assert(method.body == None)
  }

  test("method declaration with precondition") {
    val Success(method: MethodDefinition, _) = Parser.parseDef("""
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
    val Success(method: MethodDefinition, _) = Parser.parseDef("int magnitude(int x, int y);")
    val List(arg1, arg2) = method.arguments
    assert(arg1.id == "x")
    assert(arg1.valueType.asInstanceOf[NamedType].id == "int")
    assert(arg2.id == "y")
    assert(arg2.valueType.asInstanceOf[NamedType].id == "int")
  }

  test("method with body") {
    val Success(method: MethodDefinition, _) = Parser.parseDef("""
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
    val Success(use: UseDeclaration, _) = Parser.parseDef("#use <mylib>")
    assert(use.path.raw == "<mylib>")
    assert(use.path == "mylib")
    assert(use.isLibrary)
  }

  test("use path declaration") {
    val Success(use: UseDeclaration, _) = Parser.parseDef("#use \"test.c0\"")
    assert(use.path.raw == "\"test.c0\"")
    assert(use.path == "test.c0")
    assert(!use.isLibrary)
  }
}