package gvc.analyzer
import gvc.parser._

sealed trait ResolvedExpression extends ResolvedNode {
  def valueType: ResolvedType
}

case class ResolvedVariableRef(
  parsed: Node,
  variable: Option[ResolvedVariable],
) extends ResolvedExpression {
  def valueType = variable match {
    case Some(varDef) => varDef.valueType
    case None => UnknownType
  }

  def isMissing = variable.isEmpty
}

case class ResolvedInvoke(
  parsed: Node,
  method: Option[ResolvedMethodDeclaration],
  methodName: String,
  arguments: List[ResolvedExpression]
) extends ResolvedExpression {
  def valueType: ResolvedType = method match {
    case Some(declaration) => declaration.returnType
    case None => UnknownType
  }
}

case class ResolvedMember(
  parsed: Node,
  parent: ResolvedExpression,
  field: Option[ResolvedStructField],
  fieldName: String,
  isArrow: Boolean
) extends ResolvedExpression {
  def valueType = field match {
    case None => UnknownType
    case Some(field) => field.valueType
  }
}

case class ResolvedArrayIndex(
  parsed: Node,
  array: ResolvedExpression,
  index: ResolvedExpression
) extends ResolvedExpression {
  def valueType = array.valueType match {
    case ResolvedArray(valueType) => valueType
    case _ => UnknownType
  }
}

sealed trait ArithmeticOperation
object ArithmeticOperation {
  case object Add extends ArithmeticOperation
  case object Subtract extends ArithmeticOperation
  case object Divide extends ArithmeticOperation
  case object Multiply extends ArithmeticOperation
}

case class ResolvedArithmetic(
  parsed: BinaryExpression,
  left: ResolvedExpression,
  right: ResolvedExpression,
  operation: ArithmeticOperation,
) extends ResolvedExpression {
  def valueType = IntType
}

sealed trait ComparisonOperation
object ComparisonOperation {
  case object EqualTo extends ComparisonOperation
  case object NotEqualTo extends ComparisonOperation
  case object LessThan extends ComparisonOperation
  case object GreaterThan extends ComparisonOperation
  case object GreaterThanOrEqualTo extends ComparisonOperation
  case object LessThanOrEqualTo extends ComparisonOperation
}

case class ResolvedComparison(
  parsed: BinaryExpression,
  left: ResolvedExpression,
  right: ResolvedExpression,
  operation: ComparisonOperation
) extends ResolvedExpression {
  def valueType = BoolType
}

case class ResolvedTernary(
  parsed: TernaryExpression,
  condition: ResolvedExpression,
  ifTrue: ResolvedExpression,
  ifFalse: ResolvedExpression
) extends ResolvedExpression {
  def valueType = {
    // Avoid propagating NULL if possible
    val trueType = ifTrue.valueType
    val falseType = ifFalse.valueType
    if (trueType == NullType) falseType
    else trueType
  }
}

sealed trait LogicalOperation
object LogicalOperation {
  case object Or extends LogicalOperation
  case object And extends LogicalOperation
}

case class ResolvedLogical(
  parsed: Node,
  left: ResolvedExpression,
  right: ResolvedExpression,
  operation: LogicalOperation,
) extends ResolvedExpression {
  def valueType: ResolvedType = BoolType
}

case class ResolvedDereference(
  parsed: UnaryExpression,
  value: ResolvedExpression,
) extends ResolvedExpression {
  def valueType: ResolvedType = value.valueType match {
    case ResolvedPointer(valueType) => valueType
    case _ => UnknownType
  }
}

case class ResolvedNot(
  parsed: UnaryExpression,
  value: ResolvedExpression,
) extends ResolvedExpression {
  def valueType = BoolType
}

case class ResolvedNegation(
  parsed: UnaryExpression,
  value: ResolvedExpression
) extends ResolvedExpression {
  def valueType = IntType
}

case class ResolvedAlloc(
  parsed: AllocExpression,
  memberType: ResolvedType
) extends ResolvedExpression {
  def valueType = ResolvedPointer(memberType)
}

case class ResolvedAllocArray(
  parsed: AllocArrayExpression,
  memberType: ResolvedType,
  length: ResolvedExpression
) extends ResolvedExpression {
  def valueType = ResolvedArray(memberType)
}

sealed trait ResolvedLiteral extends ResolvedExpression {
  def value: Any
}

case class ResolvedString(parsed: StringExpression) extends ResolvedLiteral {
  def value = parsed.value
  def valueType = StringType
}

case class ResolvedChar(parsed: CharacterExpression) extends ResolvedLiteral {
  def value = parsed.value
  def valueType = CharType
}

case class ResolvedInt(parsed: IntegerExpression) extends ResolvedLiteral {
  def value = parsed.value
  def valueType = IntType
}

case class ResolvedBool(parsed: BooleanExpression) extends ResolvedLiteral {
  def value = parsed.value
  def valueType = BoolType
}

case class ResolvedNull(parsed: NullExpression) extends ResolvedLiteral {
  def value = null
  def valueType = NullType
}