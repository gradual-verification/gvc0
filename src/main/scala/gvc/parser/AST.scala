package gvc.parser

sealed trait AstNode
sealed trait AstExpression extends AstNode
sealed trait AstType extends AstNode
sealed trait Specification
sealed trait AstStatement extends AstNode {
  val specifications: List[Specification]
  def withSpecifications(specs: List[Specification]): AstStatement
}
sealed trait AstDefinition extends AstNode

case class LineColPosition(line: Int, col: Int)

sealed trait LiteralExpression extends AstExpression {
  val raw: String
  val value: Any
}

case class TypeDefinition(name: String, value: AstType) extends AstDefinition
case class StructDefinition(name: String, fields: Option[List[MemberDefinition]]) extends AstDefinition
case class UseDeclaration(path: StringExpression, library: Boolean) extends AstDefinition
case class MethodDefinition(name: String, returnType: AstType, arguments: List[MemberDefinition], body: Option[BlockStatement], specifications: List[Specification]) extends AstDefinition
case class MemberDefinition(name: String, memberType: AstType) extends AstNode

case class RequiresSpecification(value: AstExpression) extends Specification
case class EnsuresSpecification(value: AstExpression) extends Specification
case class LoopInvariantSpecification(value: AstExpression) extends Specification
case class AssertSpecification(value: AstExpression) extends Specification

case class ExpressionStatement(expression: AstExpression, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): ExpressionStatement = copy(specifications = specs)
}
case class AssignmentStatement(left: AstExpression, op: AssignOp.Value, right: AstExpression, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): AssignmentStatement = copy(specifications = specs)
}
case class UnaryOperationStatement(value: AstExpression, op: UnaryOp.Value, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): UnaryOperationStatement = copy(specifications = specs)
}
case class VariableStatement(varType: AstType, varId: String, value: Option[AstExpression], specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): VariableStatement = copy(specifications = specs)
}
case class IfStatement(condition: AstExpression, body: AstStatement, elseStmt: Option[AstStatement], specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): IfStatement = copy(specifications = specs)
}
case class WhileStatement(condition: AstExpression, body: AstStatement, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): WhileStatement = copy(specifications = specs)
}
case class ForStatement(declaration: AstStatement, condition: AstExpression, incrementor: AstStatement, body: AstStatement, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): ForStatement = copy(specifications = specs)
}
case class ReturnStatement(value: Option[AstExpression], specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): ReturnStatement = copy(specifications = specs)
}
case class AssertStatement(value: AstExpression, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): AssertStatement = copy(specifications = specs)
}
case class ErrorStatement(value: AstExpression, specifications: List[Specification] = List.empty) extends AstStatement {
  def withSpecifications(specs: List[Specification]): ErrorStatement = copy(specifications = specs)
}
case class BlockStatement(body: List[AstStatement], specifications: List[Specification], postSpecifications: List[Specification]) extends AstStatement {
  def withSpecifications(specs: List[Specification]): BlockStatement = copy(specifications = specs)
}

case class VariableExpression(ident: String) extends AstExpression
case class StringExpression(raw: String, value: String) extends LiteralExpression
case class CharacterExpression(raw: String, value: Char) extends LiteralExpression
case class IntegerExpression(raw: String, value: Int) extends LiteralExpression
case class BooleanExpression(raw: String, value: Boolean) extends LiteralExpression
case class NullExpression(raw: String = "NULL", value: Null) extends LiteralExpression
case class BinaryExpression(left: AstExpression, right: AstExpression, op: BinaryOp.Value) extends AstExpression
case class UnaryExpression(operand: AstExpression, op: UnaryOp.Value) extends AstExpression
case class TernaryOperation(check: AstExpression, left: AstExpression, right: AstExpression) extends AstExpression
case class InvokeExpression(ident: String, arguments: List[AstExpression] = List[AstExpression]()) extends AstExpression
case class MemberExpression(parent: AstExpression, field: String) extends AstExpression
case class MemberDerefExpression(parent: AstExpression, field: String) extends AstExpression
case class IndexExpression(parent: AstExpression, index: AstExpression) extends AstExpression
case class AllocExpression(memberType: AstType) extends AstExpression
case class AllocArrayExpression(memberType: AstType, length: AstExpression) extends AstExpression

case class NamedType(name: String) extends AstType
case class NamedStructType(name: String) extends AstType
case class PointerType(valueType: AstType) extends AstType
case class ArrayType(valueType: AstType) extends AstType

object BinaryOp extends Enumeration {
  type BinaryOp = Value
  
  val LogicalOr = Value("||")
  val LogicalAnd = Value("&&")
  val BitwiseOr = Value("|")
  val BitwiseXor = Value("^")
  val BitwiseAnd = Value("&")
  val Equal = Value("==")
  val NotEqual = Value("!=")
  val Less = Value("<")
  val LessEqual = Value("<=")
  val GreaterEqual = Value(">=")
  val Greater = Value(">")
  val ShiftLeft = Value("<<")
  val ShiftRight = Value(">>")
  val Add = Value("+")
  val Subtract = Value("-")
  val Multiply = Value("*")
  val Divide = Value("/")
  val Modulus = Value("%")
}

object UnaryOp extends Enumeration {
  type UnaryOp = Value

  val Not = Value("!")
  val BitwiseNot = Value("~")
  val Negate = Value("-")
  val Deref = Value("*")

  val Increment = Value("++")
  val Decrement = Value("--")
}

object AssignOp extends Enumeration {
  type AssignmentOp = Value
  val Assign = Value("=")
  val Add = Value("+=")
  val Subtract = Value("-=")
  val Multiply = Value("*=")
  val Divide = Value("/=")
  val Modulus = Value("%=")
  val ShiftLeft = Value("<<=")
  val ShiftRight = Value(">>=")
  val BitwiseAnd = Value("&=")
  val BitwiseOr = Value("|=")
  val BitwiseXor = Value("^=")
}