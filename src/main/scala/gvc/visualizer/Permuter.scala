package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.visualizer.PermuteMode.{Append, Linear, PermuteMode}
import gvc.visualizer.PermuteTarget.{All, Field, PermuteTarget, Predicate}

import scala.collection.mutable.ListBuffer

object PermuteMode extends Enumeration {
  type PermuteMode = Value
  val Exp, Linear, Append = Value
}
object PermuteTarget extends Enumeration {
  type PermuteTarget = Value
  val Expr, Predicate, Field, All = Value
}

abstract class Permuter[T, S]() {
  final var contents: ListBuffer[ListBuffer[T]] = ListBuffer()
  private final def permuteExp(toPermute: S): Unit = {
    contents ++= contents.map(linearLayer => {
      linearLayer.map(marker => {
        combine(marker, toPermute)
      })
    })
  }
  private final def permuteLinear(toPermute: S): Unit = {
    val lastLinear = contents.last
    contents += lastLinear.map(marker => {
      combine(marker, toPermute)
    })
  }
  private final def append(toAppend: S): Unit = {
    contents = contents.map(linear => {
      linear.map(append => {
        combine(append, toAppend)
      })
    })
  }
  def permute(toPermute: S, modeMap: Map[PermuteTarget, PermuteMode]): Unit = {
    getPermuteMode(toPermute, modeMap) match {
      case gvc.visualizer.PermuteMode.Exp    => permuteExp(toPermute)
      case gvc.visualizer.PermuteMode.Linear => permuteLinear(toPermute)
      case gvc.visualizer.PermuteMode.Append => append(toPermute)
    }
  }
  def combine(
      root: T,
      toAppend: S
  ): T

  def getPermuteMode(
      toPermute: S,
      modeMap: Map[PermuteTarget, PermuteMode]
  ): PermuteMode

  final def gather(): List[T] = {
    contents.flatMap(_.map(item => { item })).toList
  }

}

class BlockPermuter extends Permuter[PermutedBlock, PermutedOp] {
  contents += ListBuffer(PermutedBlock(0, 0, List()))
  override def combine(
      root: PermutedBlock,
      toAppend: PermutedOp
  ): PermutedBlock = {
    PermutedBlock(
      root.nClausesAssertions + toAppend.nClausesAssertions,
      root.nClausesLoopInvariants + toAppend.nCLausesLoopInvariants,
      if (toAppend.op.isDefined) root.opList ++ List(toAppend.op.get)
      else root.opList
    )
  }
  override def getPermuteMode(
      toPermute: PermutedOp,
      modeMap: Map[PermuteTarget, PermuteMode]
  ): PermuteMode = Append
}

class ExpressionPermuter
    extends Permuter[PermutedExpression, PermutedExpression] {
  contents += ListBuffer(PermutedExpression(0, None))
  override def combine(
      root: PermutedExpression,
      toAppend: PermutedExpression
  ): PermutedExpression = {
    root.expr match {
      case Some(rootExpr) =>
        toAppend.expr match {
          case Some(appendExpr) =>
            PermutedExpression(
              root.nClauses + toAppend.nClauses,
              Some(
                new IRGraph.Binary(IRGraph.BinaryOp.And, rootExpr, appendExpr)
              )
            )
          case None => {
            root
          }
        }
      case None => toAppend
    }

  }
  override def getPermuteMode(
      toPermute: PermutedExpression,
      modeMap: Map[PermuteTarget, PermuteMode]
  ): PermuteMode = {
    toPermute.expr match {
      case Some(expr) =>
        expr match {
          case _: IRGraph.Accessibility =>
            modeMap.getOrElse(Field, Linear)
          case _: IRGraph.PredicateInstance =>
            modeMap.getOrElse(Predicate, Linear)
          case _ => modeMap.getOrElse(All, Linear)
        }
      case None => Append
    }
  }
}
