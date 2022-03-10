package gvc.permutation
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

object SpecType extends Enumeration {
  type SpecType = Value
  val Assert, Precondition, Postcondition, Fold, Unfold, Invariant, Predicate =
    Value
}

object ExprType extends Enumeration {
  type ExprType = Any
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
      template: IRGraph.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    currentContext = Some(parent)
    specIndex += 1
  }

  def visitOp(parent: Either[Method, Predicate], template: IRGraph.Op): Unit = {
    currentContext = Some(parent)
  }

  def visit(input: IRGraph.Program): O = {
    new SpecTraversal[I, O]().visitAST(input, this)
    val output = collectOutput()
    reset()
    output
  }

  def collectAssertion(): Unit
  def collectIf(stmt: IRGraph.If): Unit
  def collectConditional(cond: IRGraph.Conditional): Unit
  def collectWhile(whl: IRGraph.While): Unit

  def enterExpr(): Unit
  def leaveExpr(): Unit
  def enterBlock(): Unit
  def leaveBlock(): Unit

  def leavePredicate(): Unit
  def leaveMethod(): Unit

  def collectOutput(): O
}

class SpecTraversal[I, O] {
  def visitAST(program: IRGraph.Program, visitor: SpecVisitor[I, O]): Unit = {
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
    visitExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression),
      visitor
    )
    visitor.leavePredicate()
  }

  private def visitMethod(method: Method, visitor: SpecVisitor[I, O]): Unit = {
    if (method.name == "list_insert") {
      print("hi")
    }
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
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
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
        case _: IRGraph.Fold =>
          visitor.visitSpec(
            Left(context),
            op,
            SpecType.Fold,
            ExprType.Predicate
          )
        case _: IRGraph.Unfold =>
          visitor.visitSpec(
            Left(context),
            op,
            SpecType.Unfold,
            ExprType.Predicate
          )
        case ifstmt: IRGraph.If =>
          visitBlock(context, ifstmt.ifTrue, visitor)
          visitBlock(context, ifstmt.ifFalse, visitor)
          visitor.collectIf(ifstmt)
        case whl: IRGraph.While =>
          visitExpression(
            Left(context),
            SpecType.Invariant,
            whl.invariant,
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
          case _: IRGraph.Accessibility =>
            visitor.visitSpec(
              context,
              expr,
              specType,
              ExprType.Accessibility
            )
          case _: IRGraph.PredicateInstance =>
            visitor.visitSpec(
              context,
              expr,
              specType,
              ExprType.Predicate
            )
          case imprecise: IRGraph.Imprecise =>
            buildExpression(
              context,
              specType,
              imprecise.precise,
              visitor
            )
          case conditional: IRGraph.Conditional =>
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
          case binary: IRGraph.Binary =>
            if (binary.operator == IRGraph.BinaryOp.And) {
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
            visitor.visitSpec(
              context,
              expr,
              specType,
              exprType = ExprType.Default
            )
        }
      case None =>
    }
  }
}
