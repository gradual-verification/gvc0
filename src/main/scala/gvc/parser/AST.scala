package gvc.parser

sealed trait Node{
  val span: SourceSpan
}

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
case class NamedType(id: Identifier, span: SourceSpan) extends Type
case class NamedStructType(id: Identifier, span: SourceSpan) extends Type
case class PointerType(valueType: Type, span: SourceSpan) extends Type
case class ArrayType(valueType: Type, span: SourceSpan) extends Type

// Expressions
sealed trait Expression extends Node
case class VariableExpression(variable: Identifier, span: SourceSpan) extends Expression
case class IncrementExpression(value: Expression, operator: IncrementOperator, span: SourceSpan) extends Expression
case class BinaryExpression(left: Expression, operator: BinaryOperator.Value, right: Expression, span: SourceSpan) extends Expression
case class UnaryExpression(operand: Expression, operator: UnaryOperator.Value, span: SourceSpan) extends Expression
case class TernaryExpression(condition: Expression, ifTrue: Expression, ifFalse: Expression, span: SourceSpan) extends Expression
case class InvokeExpression(method: Identifier, arguments: List[Expression], span: SourceSpan) extends Expression
case class AllocExpression(valueType: Type, span: SourceSpan) extends Expression
case class AllocArrayExpression(valueType: Type, length: Expression, span: SourceSpan) extends Expression
case class IndexExpression(parent: Expression, index: Expression, span: SourceSpan) extends Expression
case class MemberExpression(parent: Expression, field: Identifier, isArrow: Boolean, span: SourceSpan) extends Expression
case class ResultExpression(span: SourceSpan) extends Expression
case class LengthExpression(value: Expression, span: SourceSpan) extends Expression
case class ImprecisionExpression(span: SourceSpan) extends Expression
case class AccessibilityExpression(field: Expression, span: SourceSpan) extends Expression

// Literal expressions
sealed trait LiteralExpression extends Expression {
  val raw: String
  val value: Any
}

case class StringExpression(raw: String, value: String, span: SourceSpan) extends LiteralExpression {
  def ==(other: String): Boolean = {
    value == other
  }
}

case class CharacterExpression(raw: String, value: Char, span: SourceSpan) extends LiteralExpression {
  def ==(other: Char): Boolean = {
    value == other
  }
}

case class IntegerExpression(raw: String, value: Int, span: SourceSpan) extends LiteralExpression {
  def ==(other: Int): Boolean = {
    value == other
  }
}

case class BooleanExpression(raw: String, value: Boolean, span: SourceSpan) extends LiteralExpression {
  def ==(other: Boolean): Boolean = {
    value == other
  }
}

case class NullExpression(raw: String = "NULL", value: Null, span: SourceSpan) extends LiteralExpression {
  def ==(other: Null): Boolean = true
}

// SpecExprifications
sealed trait SpecExprification extends Node
case class RequiresSpecExprification(value: Expression, span: SourceSpan) extends SpecExprification
case class EnsuresSpecExprification(value: Expression, span: SourceSpan) extends SpecExprification
case class LoopInvariantSpecExprification(value: Expression, span: SourceSpan) extends SpecExprification
case class AssertSpecExprification(value: Expression, span: SourceSpan) extends SpecExprification
case class FoldSpecExprification(predicate: Identifier, arguments: List[Expression], span: SourceSpan) extends SpecExprification
case class UnfoldSpecExprification(predicate: Identifier, arguments: List[Expression], span: SourceSpan) extends SpecExprification

// Statements
sealed trait Statement extends Node {
  val specifications: List[SpecExprification]
  def withSpecExprifications(specs: List[SpecExprification]): Statement
}

case class ExpressionStatement(
  expression: Expression,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): ExpressionStatement = copy(specifications = specs)
}
case class AssignmentStatement(
  left: Expression,
  operator: AssignOperator.Value,
  right: Expression,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): AssignmentStatement = copy(specifications = specs)
}
case class VariableStatement(
  valueType: Type,
  id: Identifier,
  initialValue: Option[Expression],
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): VariableStatement = copy(specifications = specs)
}
case class IfStatement(
  condition: Expression,
  ifTrue: Statement,
  ifFalse: Option[Statement],
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): IfStatement = copy(specifications = specs)
}
case class WhileStatement(
  condition: Expression,
  body: Statement,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): WhileStatement = copy(specifications = specs)
}
case class ForStatement(
  initializer: Statement,
  condition: Expression,
  incrementor: Statement,
  body: Statement,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): ForStatement = copy(specifications = specs)
}
case class ReturnStatement(
  value: Option[Expression],
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): ReturnStatement = copy(specifications = specs)
}
case class AssertStatement(
  value: Expression,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): AssertStatement = copy(specifications = specs)
}
case class ErrorStatement(
  value: Expression,
  span: SourceSpan,
  specifications: List[SpecExprification] = List.empty
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): ErrorStatement = copy(specifications = specs)
}
case class BlockStatement(
  body: List[Statement],
  span: SourceSpan,
  specifications: List[SpecExprification],
  trailingSpecExprifications: List[SpecExprification]
) extends Statement {
  def withSpecExprifications(specs: List[SpecExprification]): BlockStatement = copy(specifications = specs)
}

// Definitions
sealed trait Definition extends Node
case class MemberDefinition(id: Identifier, valueType: Type, span: SourceSpan) extends Node
case class TypeDefinition(id: Identifier, value: Type, span: SourceSpan) extends Definition
case class StructDefinition(id: Identifier, fields: Option[List[MemberDefinition]], span: SourceSpan) extends Definition
case class UseDeclaration(path: StringExpression, isLibrary: Boolean, span: SourceSpan) extends Definition
case class PredicateDefinition(
  id: Identifier,
  arguments: List[MemberDefinition],
  body: Option[Expression],
  span: SourceSpan
) extends Definition
case class MethodDefinition(
  id: Identifier,
  returnType: Type,
  arguments: List[MemberDefinition],
  body: Option[BlockStatement],
  specifications: List[SpecExprification],
  span: SourceSpan
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
}

sealed trait IncrementOperator
object IncrementOperator {
  case object Increment extends IncrementOperator
  case object Decrement extends IncrementOperator
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