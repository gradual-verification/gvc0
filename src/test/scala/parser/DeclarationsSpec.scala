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
}