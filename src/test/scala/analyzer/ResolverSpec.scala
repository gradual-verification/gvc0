import org.scalatest.funsuite._
import gvc.parser._
import gvc.analyzer._

class ResolverSpecExpr extends AnyFunSuite {
  test("resolve empty method") {
    val input = List(
      methodDef("main", namedType("int"), List(), Some(block()))
    )

    val result = resolveSuccess(input)
    val defn = getMethod(result, "main")
    assert(defn.body.statements.isEmpty)
    assert(defn.declaration.arguments.isEmpty)
    assert(defn.declaration.returnType == IntType)
  }

  test("resolve variable declaration") {
    val input = List(
      methodDef("main", namedType("int"), List(), Some(block(
        varDef("x", namedType("int"), Some(intVal(1)))
      )))
    )

    val result = resolveSuccess(input)
    val main = getMethod(result, "main")

    val (variable :: Nil) = main.body.variableDefs
    assert(variable.name == "x")
    assert(variable.valueType == IntType)

    val assign = main.body.statements.head.asInstanceOf[ResolvedAssignment]
    assert(assign.value.asInstanceOf[ResolvedInt].value == 1)
  }

  test("identity function") {
    val input = List(
      methodDef("identity", namedType("int"), List("value" -> namedType("int")), Some(block(
        ReturnStatement(Some(varRef("value")), null)
      )))
    )

    val result = resolveSuccess(input)
    val identity = getMethod(result, "identity")

    val (arg :: Nil) = identity.declaration.arguments
    assert(arg.name == "value")

    val (stmt :: Nil) = identity.body.statements
    val ret = stmt.asInstanceOf[ResolvedReturn]
    val retval = ret.value.get.asInstanceOf[ResolvedVariableRef]
    assert(retval.variable.get.name == "value")
    assert(retval.valueType == IntType)
  }

  // Helper methods
  def methodDef(name: String, retType: Type, arguments: List[(String, Type)], body: Option[BlockStatement] = None) =
    MethodDefinition(
      id = Identifier(name, null),
      returnType = retType,
      arguments = arguments.map { case (name, typ) => MemberDefinition(Identifier(name, null), typ, null) },
      body = body,
      specifications = List.empty,
      span = null
    )

  def block(body: Statement *) = BlockStatement(body.toList, null, List(), List())
  def namedType(name: String): Type = NamedType(Identifier(name, null), null)
  def varDef(name: String, typ: Type, value: Option[Expression]) = VariableStatement(typ, Identifier(name, null), value, null)
  def varRef(name: String) = VariableExpression(Identifier(name, null), null)
  def intVal(value: Int) = IntegerExpression(value.toString(), value, null)
  def strVal(value: String) = StringExpression(value, value, null)

  def getMethod(program: ResolvedProgram, name: String): ResolvedMethodDefinition = {
    val method = program.methodDefinitions.find(_.name == name)
    assert(method.isDefined, "Method " + name + " not found")
    method.get
  }

  def resolveSuccess(program: List[Definition]): ResolvedProgram = {
    val errors = new ErrorSink()
    val resolved = Resolver.resolveProgram(program, errors)
    assert(errors.errors.isEmpty)

    resolved
  }
}