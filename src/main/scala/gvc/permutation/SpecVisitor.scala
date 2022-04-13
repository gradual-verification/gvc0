package gvc.permutation
import gvc.transformer.IR
import gvc.transformer.IR.{Block, Expression, Method, Predicate}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

object SpecType extends Enumeration {
  type SpecType = Value
  val Assert, Precondition, Postcondition, Fold, Unfold, Invariant, Predicate =
    Value
}

object ExprType extends Enumeration {
  type ExprType = Value
  val Accessibility, Predicate, Default = Value
}

abstract class SpecVisitor[I, O] {
  var specIndex = 0
  var currentContext: Option[Either[Method, Predicate]] = None

  def reset(): Unit = specIndex = 0
  def previous(): Int = this.specIndex - 1
  def visitSpec(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    currentContext = Some(parent)
    specIndex += 1
  }

  def visitSpec(
      parent: Either[Method, Predicate],
      template: IR.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    currentContext = Some(parent)
    specIndex += 1
  }

  def visitOp(parent: Either[Method, Predicate], template: IR.Op): Unit = {
    currentContext = Some(parent)
  }

  def visit(input: IR.Program): O = {
    new SpecTraversal[I, O]().visitAST(input, this)
    val output = collectOutput()
    reset()
    output
  }

  def collectAssertion(): Unit
  def collectIf(stmt: IR.If): Unit
  def collectConditional(cond: IR.Conditional): Unit
  def collectWhile(whl: IR.While): Unit

  def enterExpr(): Unit
  def leaveExpr(): Unit
  def enterBlock(): Unit
  def leaveBlock(): Unit

  def leavePredicate(): Unit
  def enterPredicate(predicate: Predicate): Unit

  def leaveMethod(): Unit
  def enterMethod(method: Method): Unit

  def collectOutput(): O
}

class SpecTraversal[I, O] {
  def visitAST(program: IR.Program, visitor: SpecVisitor[I, O]): Unit = {
    program.methods.foreach(visitMethod(_, visitor))
    program.predicates.foreach(visitPredicate(_, visitor))
  }

  class SpecVisitorException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def visitPredicate(
      predicate: Predicate,
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterPredicate(predicate)
    visitExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression),
      visitor
    )
    visitor.leavePredicate()
  }

  private def visitMethod(method: Method, visitor: SpecVisitor[I, O]): Unit = {
    visitor.enterMethod(method)

    visitExpression(
      Left(method),
      SpecType.Precondition,
      method.precondition,
      visitor
    )

    visitExpression(
      Left(method),
      SpecType.Postcondition,
      method.postcondition,
      visitor
    )

    visitBlock(
      method,
      method.body,
      visitor
    )

    visitor.leaveMethod()
  }

  private def visitBlock(
      context: Method,
      block: Block,
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterBlock()
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IR.Assert =>
          if (assert.kind == IR.AssertKind.Specification) {
            visitExpression(
              Left(context),
              SpecType.Assert,
              Some(assert.value),
              visitor
            )
            visitor.collectAssertion()
          } else {
            visitor.visitOp(Left(context), op)
          }
        case _: IR.Fold =>
          visitor.visitSpec(
            Left(context),
            op,
            SpecType.Fold,
            ExprType.Predicate
          )
        case _: IR.Unfold =>
          visitor.visitSpec(
            Left(context),
            op,
            SpecType.Unfold,
            ExprType.Predicate
          )
        case ifstmt: IR.If =>
          visitBlock(context, ifstmt.ifTrue, visitor)
          visitBlock(context, ifstmt.ifFalse, visitor)
          visitor.collectIf(ifstmt)
        case whl: IR.While =>
          visitExpression(
            Left(context),
            SpecType.Invariant,
            Some(whl.invariant),
            visitor
          )
          visitBlock(context, whl.body, visitor)
          visitor.collectWhile(whl)
        case _ => visitor.visitOp(Left(context), op)
      }
    }
    visitor.leaveBlock()
  }

  private def visitExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      visitor: SpecVisitor[I, O]
  ): Unit = {
    visitor.enterExpr()
    buildExpression(context, specType, expression, visitor)
    visitor.leaveExpr()
  }

  private def buildExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      visitor: SpecVisitor[I, O]
  ): Unit = {
    expression match {
      case Some(expr) =>
        expr match {
          case _: IR.Accessibility =>
            visitor.visitSpec(
              context,
              expr,
              specType,
              ExprType.Accessibility
            )
          case _: IR.PredicateInstance =>
            visitor.visitSpec(
              context,
              expr,
              specType,
              ExprType.Predicate
            )
          case imprecise: IR.Imprecise =>
            buildExpression(
              context,
              specType,
              imprecise.precise,
              visitor
            )
          case conditional: IR.Conditional =>
            visitExpression(
              context,
              specType,
              Some(conditional.ifTrue),
              visitor
            )
            visitExpression(
              context,
              specType,
              Some(conditional.ifFalse),
              visitor
            )
            visitor.collectConditional(conditional)
          case binary: IR.Binary =>
            if (binary.operator == IR.BinaryOp.And) {
              buildExpression(context, specType, Some(binary.right), visitor)
              buildExpression(context, specType, Some(binary.left), visitor)
            } else {
              visitor.visitSpec(
                context,
                expr,
                specType,
                exprType = ExprType.Default
              )
            }
          case _ =>
            if (!expr.isInstanceOf[IR.BoolLit]) {
              visitor.visitSpec(
                context,
                expr,
                specType,
                exprType = ExprType.Default
              )
            }
        }
      case None =>
    }
  }
}
