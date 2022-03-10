package gvc.permutation
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{
  Block,
  Expression,
  Method,
  Op,
  Predicate,
  Program
}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object PermutationGenerator {

  def generatePermutation(
      labels: List[ASTLabel],
      template: Program
  ): Program = {
    val labelBuffer = mutable.ListBuffer.empty ++ labels
    var offset = 0

    val builtMethods = template.methods
      .map(method => {
        if (labelBuffer.nonEmpty) {
          val built = buildMethod(
            labelBuffer,
            method,
            offset
          )
          offset = built.offset
          built.method
        } else {
          method
        }
      })
      .toList

    val builtPredicates = template.predicates
      .map(predicate => {
        if (labelBuffer.nonEmpty) {
          val built = buildPredicate(
            labelBuffer,
            predicate,
            offset
          )
          offset = built.offset
          built.predicate
        } else {
          predicate
        }
      })
      .toList
    template.copy(builtMethods, builtPredicates)
  }
  private def buildPredicate(
      relevantLabels: ListBuffer[ASTLabel],
      template: Predicate,
      offset: Int
  ): BuiltPredicate = {
    val built = buildExpression(
      relevantLabels,
      template.expression,
      offset
    )
    BuiltPredicate(
      template.copy(new IRGraph.Imprecise(built.expr)),
      built.offset
    )
  }

  case class BuiltMethod(method: Method, offset: Int)
  case class BuiltPredicate(predicate: Predicate, offset: Int)

  private def buildMethod(
      relevantLabels: ListBuffer[ASTLabel],
      template: Method,
      offsetStart: Int
  ): BuiltMethod = {
    var offset = offsetStart

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
    val block = buildBlock(
      ListBuffer.empty ++ relevantLabels,
      template.body,
      offset
    )
    BuiltMethod(
      template.copy(
        Some(new IRGraph.Imprecise(precondition)),
        Some(new IRGraph.Imprecise(postcondition)),
        block.lst
      ),
      block.offset
    )
  }

  def consumeLabel(
      offset: Int,
      relevantLabels: ListBuffer[ASTLabel]
  ): Option[ASTLabel] = {
    if (relevantLabels.nonEmpty) {
      val first = relevantLabels.head
      if (first.exprIndex == offset) {
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
    val root: Option[Expression] = None
  }

  private def buildBlock(
      relevantLabels: ListBuffer[ASTLabel],
      template: Block,
      baseIndex: Int
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
            if (builtAssertExpr.expr.isDefined) {
              opBuffer += new IRGraph.Assert(
                builtAssertExpr.expr.get,
                IRGraph.AssertKind.Specification
              )
            }

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
          offset = trueBranch.offset

          val falseBranch = buildBlock(relevantLabels, ifstmt.ifFalse, offset)
          offset = falseBranch.offset

          opBuffer += ifstmt.copy(trueBranch.lst, falseBranch.lst)
        case whl: IRGraph.While =>
          val invariant = if (whl.invariant.isDefined) {
            val builtInvariant =
              buildExpression(relevantLabels, whl.invariant.get, offset)
            offset = builtInvariant.offset

            Some(new IRGraph.Imprecise(builtInvariant.expr))
          } else {
            None
          }
          val builtBody = buildBlock(relevantLabels, whl.body, offset)
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
      baseIndex: Int
  ): BuiltExpression = {
    var offset = baseIndex
    template match {
      case imprec: IRGraph.Imprecise =>
        if (imprec.precise.isDefined)
          buildExpression(relevantLabels, imprec.precise.get, baseIndex)
        else {
          BuiltExpression(None, offset)
        }
      case _ =>
        template match {
          case conditional: IRGraph.Conditional =>
            val builtTrueBranch =
              buildExpression(relevantLabels, conditional.ifTrue, offset)
            offset = builtTrueBranch.offset

            val builtFalseBranch =
              buildExpression(
                relevantLabels,
                conditional.ifFalse,
                offset
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

              val builtRight =
                buildExpression(relevantLabels, binary.right, offset)
              offset = builtRight.offset

              val builtLeft =
                buildExpression(relevantLabels, binary.left, offset)
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
          case expr: Expression =>
            BuiltExpression(
              if (consumeLabel(offset, relevantLabels).isDefined) Some(expr)
              else None,
              offset + 1
            )
        }
    }
  }
}
