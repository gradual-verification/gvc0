package gvc.parser

sealed trait Node
case class SourcePosition(line: Int, column: Int, index: Int)
case class SourceSpan(start: SourcePosition, end: SourcePosition)

// Identifiers
case class Identifier(name: String, span: SourceSpan) extends Node {
  def ==(value: String): Boolean = {
    name == value
  }
}

// Types
sealed trait Type extends Node

case class NamedType(id: Identifier) extends Type
case class NamedStructType(id: Identifier) extends Type
case class PointerType(valueType: Type) extends Type
case class ArrayType(valueType: Type) extends Type

// Expressions
sealed trait Expression extends Node

case class VariableExpression(variable: Identifier) extends Expression
case class BinaryExpression(left: Expression, operator: BinaryOperator.Value, right: Expression) extends Expression
case class UnaryExpression(operand: Expression, op: UnaryOperator.Value) extends Expression
case class TernaryExpression(condition: Expression, ifTrue: Expression, ifFalse: Expression) extends Expression
case class InvokeExpression(method: Identifier, arguments: List[Expression] = List[Expression]()) extends Expression
case class AllocExpression(valueType: Type) extends Expression
case class AllocArrayExpression(valueType: Type, length: Expression) extends Expression
case class IndexExpression(parent: Expression, index: Expression) extends Expression
case class MemberExpression(parent: Expression, field: Identifier, isArrow: Boolean) extends Expression

// Literal expressions
sealed trait LiteralExpression extends Expression {
  val raw: String
  val value: Any
}

case class StringExpression(raw: String, value: String) extends LiteralExpression
case class CharacterExpression(raw: String, value: Char) extends LiteralExpression
case class IntegerExpression(raw: String, value: Int) extends LiteralExpression
case class BooleanExpression(raw: String, value: Boolean) extends LiteralExpression
case class NullExpression(raw: String = "NULL", value: Null = null) extends LiteralExpression

// Specifications
sealed trait Specification extends Node

case class RequiresSpecification(value: Expression) extends Specification
case class EnsuresSpecification(value: Expression) extends Specification
case class LoopInvariantSpecification(value: Expression) extends Specification
case class AssertSpecification(value: Expression) extends Specification

// Statements
sealed trait Statement extends Node {
  val specifications: List[Specification]
  def withSpecifications(specs: List[Specification]): Statement
}

case class ExpressionStatement(
  expression: Expression,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): ExpressionStatement = copy(specifications = specs)
}
case class AssignmentStatement(
  left: Expression,
  operator: AssignOperator.Value,
  right: Expression,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): AssignmentStatement = copy(specifications = specs)
}
case class UnaryOperationStatement(
  value: Expression,
  operator: UnaryOperator.Value,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): UnaryOperationStatement = copy(specifications = specs)
}
case class VariableStatement(
  valueType: Type,
  id: Identifier,
  initialValue: Option[Expression],
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): VariableStatement = copy(specifications = specs)
}
case class IfStatement(
  condition: Expression,
  then: Statement,
  els: Option[Statement],
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): IfStatement = copy(specifications = specs)
}
case class WhileStatement(
  condition: Expression,
  body: Statement,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): WhileStatement = copy(specifications = specs)
}
case class ForStatement(
  initializer: Statement,
  condition: Expression,
  incrementor: Statement,
  body: Statement,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): ForStatement = copy(specifications = specs)
}
case class ReturnStatement(
  value: Option[Expression],
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): ReturnStatement = copy(specifications = specs)
}
case class AssertStatement(
  value: Expression,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): AssertStatement = copy(specifications = specs)
}
case class ErrorStatement(
  value: Expression,
  specifications: List[Specification] = List.empty
) extends Statement {
  def withSpecifications(specs: List[Specification]): ErrorStatement = copy(specifications = specs)
}
case class BlockStatement(
  body: List[Statement],
  specifications: List[Specification],
  trailingSpecifications: List[Specification]
) extends Statement {
  def withSpecifications(specs: List[Specification]): BlockStatement = copy(specifications = specs)
}

// Definitions
sealed trait Definition extends Node
case class MemberDefinition(id: Identifier, valueType: Type) extends Node
case class TypeDefinition(id: Identifier, value: Type) extends Definition
case class StructDefinition(id: Identifier, fields: Option[List[MemberDefinition]]) extends Definition
case class UseDeclaration(path: StringExpression, isLibrary: Boolean) extends Definition
case class MethodDefinition(
  id: Identifier,
  returnType: Type,
  arguments: List[MemberDefinition],
  body: Option[BlockStatement],
  specifications: List[Specification]
) extends Definition

object BinaryOperator extends Enumeration {
  type BinaryOperator = Value
  
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

object UnaryOperator extends Enumeration {
  type UnaryOperator = Value

  val Not = Value("!")
  val BitwiseNot = Value("~")
  val Negate = Value("-")
  val Deref = Value("*")

  val Increment = Value("++")
  val Decrement = Value("--")
}

object AssignOperator extends Enumeration {
  type AssignOperator = Value
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