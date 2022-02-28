package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{
  Block,
  Expression,
  Method,
  Op,
  Predicate,
  Program
}
import gvc.visualizer.Labeller.{ASTLabel, LabelOrdering}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object PermutationGenerator {

  def generatePermutation(
      labels: List[ASTLabel],
      template: Program
  ): Program = {

    val predicateLabelMap = mutable.Map[String, mutable.TreeSet[ASTLabel]]()
    val methodLabelMap = mutable.Map[String, mutable.TreeSet[ASTLabel]]()
    labels.foreach(label => {
      label.parent match {
        case Left(method) =>
          methodLabelMap.getOrElseUpdate(
            method.name,
            mutable.TreeSet[ASTLabel]()(LabelOrdering)
          ) += label
        case Right(predicate) =>
          predicateLabelMap.getOrElseUpdate(
            predicate.name,
            mutable.TreeSet[ASTLabel]()(LabelOrdering)
          ) += label
      }
    })

    val builtMethods = template.methods
      .map(method => {
        buildMethod(
          ListBuffer.empty ++ methodLabelMap
            .getOrElse(
              method.name,
              mutable.TreeSet[ASTLabel]()(LabelOrdering)
            ),
          method
        )
      })
      .toList
    val builtPredicates = template.predicates
      .map(predicate => {
        buildPredicate(
          ListBuffer.empty ++ predicateLabelMap
            .getOrElse(
              predicate.name,
              mutable.TreeSet[ASTLabel]()(LabelOrdering)
            ),
          predicate
        )
      })
      .toList
    template.copy(builtMethods, builtPredicates)

  }
  private def buildPredicate(
      relevantLabels: ListBuffer[ASTLabel],
      template: Predicate
  ): Predicate = {
    template.copy(
      new IRGraph.Imprecise(
        buildExpression(
          relevantLabels,
          template.expression
        ).expr
      )
    )
  }
  private def buildMethod(
      relevantLabels: ListBuffer[ASTLabel],
      template: Method
  ): Method = {
    var offset = 0;

    def buildOptional(exprOp: Option[Expression]): Option[Expression] = {
      if (exprOp.isDefined) {
        val built = buildExpression(
          relevantLabels,
          template.precondition.get,
          offset
        )
        offset = built.offset
        built.expr
      } else {
        None
      }
    }
    val precondition = buildOptional(template.precondition)
    val postcondition = buildOptional(template.postcondition)

    template.copy(
      Some(new IRGraph.Imprecise(precondition)),
      Some(new IRGraph.Imprecise(postcondition)),
      buildBlock(
        ListBuffer.empty ++ relevantLabels,
        template.body,
        offset
      ).lst
    )
  }

  def consumeLabel(
      offset: Int,
      relevantLabels: ListBuffer[ASTLabel]
  ): Option[ASTLabel] = {
    if (relevantLabels.nonEmpty) {
      val first = relevantLabels(0)
      if (first.expressionIndex == offset) {
        Some(relevantLabels.remove(0))
      } else {
        None
      }
    } else {
      None
    }
  }

  case class BuiltBlock(lst: List[IRGraph.Op], offset: Int)

  class ExpressionBuilder() {
    val root: Option[Expression] = None;
  }

  private def buildBlock(
      relevantLabels: ListBuffer[ASTLabel],
      template: Block,
      baseIndex: Int = 0
  ): BuiltBlock = {
    val opBuffer: ListBuffer[Op] = ListBuffer.empty
    var offset = baseIndex
    val it = template.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            val builtAssertExpr =
              buildExpression(relevantLabels, assert.value, offset)
            offset = builtAssertExpr.offset
            opBuffer += new IRGraph.Assert(
              new IRGraph.Imprecise(builtAssertExpr.expr),
              IRGraph.AssertKind.Specification
            )
          } else {
            opBuffer += op
          }
        case fold: IRGraph.Fold =>
          if (consumeLabel(offset, relevantLabels).isDefined) {
            opBuffer += fold
          }
          offset += 1
        case unfold: IRGraph.Unfold =>
          if (consumeLabel(offset, relevantLabels).isDefined) {
            opBuffer += unfold
          }
          offset += 1
        case ifstmt: IRGraph.If =>
          val trueBranch = buildBlock(relevantLabels, ifstmt.ifTrue, offset)
          val falseBranch =
            buildBlock(relevantLabels, ifstmt.ifFalse, trueBranch.offset)
          offset = falseBranch.offset
          opBuffer += ifstmt.copy(trueBranch.lst, falseBranch.lst)
        case whl: IRGraph.While =>
          val invariant = if (whl.invariant.isDefined) {
            val builtInvariant =
              buildExpression(relevantLabels, whl.invariant.get, offset)
            offset = builtInvariant.offset
            builtInvariant.expr
          } else {
            None
          }
          val builtBody =
            buildBlock(relevantLabels, whl.body, offset)
          offset = builtBody.offset
          opBuffer += whl.copy(invariant, builtBody.lst)
        case op: IRGraph.Op => opBuffer += op
      }
    }
    BuiltBlock(opBuffer.toList, offset)
  }
  case class BuiltExpression(expr: Option[Expression], offset: Int)

  def buildExpression(
      relevantLabels: ListBuffer[ASTLabel],
      template: Expression,
      baseIndex: Int = 0
  ): BuiltExpression = {
    var offset = baseIndex
    template match {
      case conditional: IRGraph.Conditional =>
        val builtTrueBranch =
          buildExpression(relevantLabels, conditional.ifTrue, offset)
        val builtFalseBranch =
          buildExpression(
            relevantLabels,
            conditional.ifFalse,
            builtTrueBranch.offset
          )
        offset = builtFalseBranch.offset
        builtTrueBranch.expr match {
          case Some(tBranch) =>
            builtFalseBranch.expr match {
              case Some(fBranch) =>
                BuiltExpression(
                  Some(
                    new IRGraph.Conditional(
                      conditional.condition,
                      tBranch,
                      fBranch
                    )
                  ),
                  offset
                )
              case None => BuiltExpression(builtTrueBranch.expr, offset)
            }
          case None =>
            builtFalseBranch.expr match {
              case Some(_) => BuiltExpression(builtFalseBranch.expr, offset)
              case None    => BuiltExpression(None, offset);
            }
        }
      case binary: IRGraph.Binary =>
        if (binary.operator == IRGraph.BinaryOp.And) {
          val builtRight = buildExpression(relevantLabels, binary.right, offset)
          val builtLeft =
            buildExpression(relevantLabels, binary.left, builtRight.offset)

          offset = builtLeft.offset
          if (builtRight.expr.isDefined) {
            if (builtLeft.expr.isDefined) {
              BuiltExpression(
                Some(
                  new IRGraph.Binary(
                    IRGraph.BinaryOp.And,
                    builtLeft.expr.get,
                    builtRight.expr.get
                  )
                ),
                offset
              )
            } else {
              BuiltExpression(
                builtRight.expr,
                offset
              )
            }
          } else {
            BuiltExpression(
              builtLeft.expr,
              offset
            )
          }
        } else {
          BuiltExpression(
            if (consumeLabel(offset, relevantLabels).isDefined) Some(binary)
            else None,
            offset + 1
          )
        }
      case expr: IRGraph.Expression =>
        BuiltExpression(
          if (consumeLabel(offset, relevantLabels).isDefined) Some(expr)
          else None,
          offset + 1
        )
    }
  }
}
