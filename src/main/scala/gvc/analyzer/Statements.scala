package gvc.analyzer
import gvc.parser._

sealed trait ResolvedStatement extends ResolvedNode

case class ResolvedExpressionStatement (
  parsed: Statement,
  value: ResolvedExpression,
) extends ResolvedStatement

case class ResolvedAssignment(
  // Assignments can be generated from variable declarations
  // or regular assignments
  parsed: Statement,
  left: ResolvedExpression,
  value: ResolvedExpression,
  operation: Option[ArithmeticOperation],
) extends ResolvedStatement

sealed trait IncrementOperation
object IncrementOperation {
  case object Increment extends IncrementOperation
  case object Decrement extends IncrementOperation
}

case class ResolvedIncrement(
  parsed: UnaryOperationStatement,
  value: ResolvedExpression,
  operation: IncrementOperation,
) extends ResolvedStatement

case class ResolvedIf(
  parsed: IfStatement,
  condition: ResolvedExpression,
  ifTrue: ResolvedStatement,
  ifFalse: Option[ResolvedStatement],
) extends ResolvedStatement

case class ResolvedWhile(
  parsed: WhileStatement,
  condition: ResolvedExpression,
  body: ResolvedStatement,
  invariant: Option[ResolvedExpression],
) extends ResolvedStatement

case class ResolvedReturn(
  parsed: ReturnStatement,
  value: Option[ResolvedExpression],
) extends ResolvedStatement

case class ResolvedAssert(
  // Asserts can come from specs or assert statements
  parsed: Node,
  value: ResolvedExpression,
) extends ResolvedStatement

case class ResolvedError(
  parsed: Node,
  value: ResolvedExpression
) extends ResolvedStatement

case class ResolvedBlock(
  parsed: Statement,
  variableDefs: List[ResolvedVariable],
  statements: List[ResolvedStatement]
) extends ResolvedStatement
