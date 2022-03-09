package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SpecType.{Postcondition, Precondition, SpecType}

import scala.collection.mutable.ListBuffer

/*
abstract class SpecExpressionTraversal[A](
) {
  case class ASTOffset(labels: List[A])

  class SpecTraversalException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  def exec(program: IRGraph.Program)

  def traverseBlock(
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
                Some(SpecType.Assert),
                Some(assert.value),
                offset
              )
            offset += specAssertOffset.labels.length
            astLabelBuffer ++= specAssertOffset.labels
          }
        case fold: IRGraph.Fold =>
          astLabelBuffer += specOperation(
            Left(context),
            offset,
            fold,
            Some(SpecType.Fold),
            ExprType.Predicate
          )
          offset += 1
        case unfold: IRGraph.Unfold =>
          astLabelBuffer += specOperation(
            Left(context),
            offset,
            unfold,
            Some(SpecType.Unfold),
            ExprType.Predicate
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
              Some(SpecType.Invariant),
              whl.invariant,
              offset
            )
          offset += invariantOffset.labels.length
          val whlBlockOffset =
            traverseBlock(context, whl.body, offset)
          offset += whlBlockOffset.labels.length
          astLabelBuffer ++= invariantOffset.labels ++ whlBlockOffset.labels

        case op => specOperation(Left(context), offset, op)
      }
    }
    ASTOffset(astLabelBuffer.toList)
  }

  def traverseExpression(
      context: Either[Method, Predicate],
      specType: Option[SpecType],
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
              astLabelBuffer += specExpression(
                context,
                offset,
                acc,
                specType,
                ExprType.Accessibility
              )
              offset += 1
            case pred: IRGraph.PredicateInstance =>
              astLabelBuffer += specExpression(
                context,
                offset,
                pred,
                specType,
                ExprType.Predicate
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
                specExpression(
                  context,
                  offset,
                  binary,
                  specType
                )
              }
            case _ =>
              specExpression(
                context,
                offset,
                _,
                specType
              )
          }
        }
        ASTOffset(astLabelBuffer.toList)
      case None => ASTOffset(List.empty)
    }
  }

  def specOperation(
                     parentContext: Either[Method, Predicate],
                     exprIndex: Int,
                     template: IRGraph.Op,
                     specType: Option[SpecType] = None,
                     exprType: ExprType = ExprType.Default
  ): A

  def specExpression(
      parentContext: Either[Method, Predicate],
      expressionIndex: Int,
      template: IRGraph.Expression,
      specType: Option[SpecType] = None,
      exprType: ExprType = ExprType.Default
  ): A
}

class LabelSpecs extends SpecExpressionTraversal[ASTLabel] {

  override def exec(program: IRGraph.Program): Unit = {
    val predicateLabels = program.predicates.flatMap(pred => traverseExpression(Right(pred), specType = Some(SpecType.Predicate), expression = Some(pred.expression)).labels)
    val methodLabels = program.methods.flatMap(method => {
      val precondition = traverseExpression(Left(method), specType = Some(Precondition), expression = method.precondition)
      val postcondition = traverseExpression(Left(method), specType = Some(Postcondition), expression = method.precondition)
      val body = traverseBlock(method, method.body)
      precondition.labels ++ postcondition.labels ++ body.labels
    })
    predicateLabels ++ methodLabels
  }

  override def visitOperation(parentContext: Either[Method, Predicate], exprIndex: Int, template: IRGraph.Op, specType: Option[SpecType], exprType: ExprType): List[ASTLabel]  = {
    if(specType.isDefined){
      List(new ASTLabel(parentContext, specType.get, exprType, exprIndex))
    }else{
      List.empty
    }
  }

  override def visitExpression(parentContext: Either[Method, Predicate], expressionIndex: Int, template: Expression, specType: Option[SpecType], exprType: ExprType): ASTLabel = {
    if(specType.isDefined) {
      new ASTLabel()
    }else{
      new ASTLabel()
    }
  }

}
*/

