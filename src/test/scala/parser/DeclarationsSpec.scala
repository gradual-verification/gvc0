import org.scalatest.funsuite._
import gvc.parser._
import fastparse.Parsed.{Success, Failure}

class DeclarationsSpec extends AnyFunSuite {
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
    val MemberDefinition(name1, type1: NamedType) = field1
    assert(name1 == "field1")
    assert(type1.id == "int")

    val MemberDefinition(name2, type2: NamedType) = field2
    assert(name2 == "field2")
    assert(type2.id == "string")
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
    val MethodDefinition(name, _, args, None, _) = method
    val List(arg1, arg2) = args
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
    assert(stmt3.isInstanceOf[UnaryOperationStatement])
  }

  test("use library declaration") {
    val Success(UseDeclaration(path, isLibrary), _) = Parser.parseDef("#use <mylib>")
    val StringExpression(raw, value, _) = path
    assert(raw == "<mylib>")
    assert(value == "mylib")
    assert(isLibrary)
  }

  test("use path declaration") {
    val Success(UseDeclaration(path, isLibrary), _) = Parser.parseDef("#use \"test.c0\"")
    val StringExpression(raw, value, _) = path
    assert(raw == "\"test.c0\"")
    assert(value == "test.c0")
    assert(!isLibrary)
  }
}