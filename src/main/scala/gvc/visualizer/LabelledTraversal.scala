package gvc.visualizer

import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SpecType.SpecType

import scala.collection.mutable.ListBuffer

abstract class SpecExpressionTraversal[A](
) {

  case class ASTOffset(labels: List[A])

  class SpecTraversalException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def traverseBlock(
      context: Method,
      block: Block,
      baseIndex: Int = 0
  ): ASTOffset = {
    val astLabelBuffer: ListBuffer[A] = ListBuffer()
    var offset = baseIndex
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            val specAssertOffset =
              traverseExpression(
                Left(context),
                SpecType.Assert,
                Some(assert.value),
                offset
              )
            offset += specAssertOffset.labels.length
            astLabelBuffer ++= specAssertOffset.labels
          }
        case fold: IRGraph.Fold =>
          astLabelBuffer += traversedOperation(
            Left(context),
            offset,
            fold
          )
          offset += 1
        case unfold: IRGraph.Unfold =>
          astLabelBuffer += traversedOperation(
            Left(context),
            offset,
            unfold
          )
          offset += 1
        case ifstmt: IRGraph.If =>
          val trueBranchOffset = traverseBlock(context, ifstmt.ifTrue, offset)
          offset += trueBranchOffset.labels.length

          val falseBranchOffset =
            traverseBlock(
              context,
              ifstmt.ifFalse,
              offset + trueBranchOffset.labels.length
            )
          offset += falseBranchOffset.labels.length

          astLabelBuffer ++= trueBranchOffset.labels ++ falseBranchOffset.labels
        case whl: IRGraph.While =>
          val invariantOffset =
            traverseExpression(
              Left(context),
              SpecType.Invariant,
              whl.invariant,
              offset
            )
          offset += invariantOffset.labels.length
          val whlBlockOffset =
            traverseBlock(context, whl.body, offset)
          offset += whlBlockOffset.labels.length
          astLabelBuffer ++= invariantOffset.labels ++ whlBlockOffset.labels

        case op => traversedOperation(Left(context), offset, op)
      }
    }
    ASTOffset(astLabelBuffer.toList)
  }

  private def traverseExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      baseIndex: Int = 0
  ): ASTOffset = {

    expression match {
      case Some(expr) =>
        val astLabelBuffer: ListBuffer[A] = ListBuffer()
        val exprStack = ListBuffer(expr)
        var offset = baseIndex
        while (exprStack.nonEmpty) {
          val top = exprStack.remove(exprStack.length - 1)
          top match {
            case acc: IRGraph.Accessibility =>
              astLabelBuffer += traversedExpression(
                context,
                specType,
                ExprType.Accessibility,
                offset,
                acc
              )
              offset += 1
            case pred: IRGraph.PredicateInstance =>
              astLabelBuffer += traversedExpression(
                context,
                specType,
                ExprType.Predicate,
                offset,
                pred
              )
              offset += 1
            case imprecise: IRGraph.Imprecise =>
              traverseExpression(
                context,
                specType,
                imprecise.precise,
                baseIndex
              )
            case conditional: IRGraph.Conditional =>
              val trueBranchOffset = traverseExpression(
                context,
                specType,
                Some(conditional.ifTrue),
                offset
              )
              offset += trueBranchOffset.labels.length

              val falseBranchOffset = traverseExpression(
                context,
                specType,
                Some(conditional.ifFalse),
                offset
              )
              offset += falseBranchOffset.labels.length

              astLabelBuffer ++= trueBranchOffset.labels ++ falseBranchOffset.labels
            case binary: IRGraph.Binary =>
              if (binary.operator == IRGraph.BinaryOp.And) {
                exprStack += binary.left
                exprStack += binary.right
              } else {
                traversedExpression(
                  context,
                  specType,
                  ExprType.Default,
                  offset,
                  binary
                )
              }
            case _ =>
              traversedExpression(
                context,
                specType,
                ExprType.Default,
                offset,
                _
              )
          }
        }
        ASTOffset(astLabelBuffer.toList)
      case None => ASTOffset(List.empty)
    }
  }

  def traversedOperation(
      parentContext: Either[Method, Predicate],
      expressionIndex: Int,
      template: IRGraph.Op
  ): A

  def traversedExpression(
      parentContext: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int,
      template: IRGraph.Expression
  ): A
}

class LabelSpecs extends SpecExpressionTraversal[ASTLabel] {
  override def traversedOperation(
      parentContext: Either[Method, Predicate],
      expressionIndex: Int,
      template: IRGraph.Op
  ): ASTLabel = ???

  override def traversedExpression(
      parentContext: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int,
      template: Expression
  ): ASTLabel = ???

}

class BuildProgram extends SpecExpressionTraversal[ASTLabel] {
  override def traversedOperation(
      parentContext: Either[Method, Predicate],
      expressionIndex: Int,
      template: IRGraph.Op
  ): ASTLabel = ???

  override def traversedExpression(
      parentContext: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int,
      template: Expression
  ): ASTLabel = ???

}
