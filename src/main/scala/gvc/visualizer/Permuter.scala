package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.visualizer.PermuteMode.{Append, Linear, PermuteMode}
import gvc.visualizer.PermuteTarget.{All, Field, PermuteTarget, Predicate}

import scala.collection.mutable.ListBuffer
case class ProgramPermutation(
    ir: IRGraph.Program,
    source: String,
    nClausesPreconditions: Int,
    nClausesPostconditions: Int,
    nClausesAssertions: Int,
    nCLausesLoopInvariants: Int,
    methodMetadata: Map[String, PermutedMethod]
)

case class PermutedExpression(
    nClauses: Int,
    expr: Option[IRGraph.Expression]
)

case class PermutationMetadata(
    nClausesPreconditions: Int,
    nClausesPostconditions: Int
)

case class PermutedMethod(
    method: IRGraph.Method,
    nClausesPreconditions: Int = 0,
    nClausesPostconditions: Int = 0,
    nClausesAssertions: Int = 0,
    nClausesLoopInvariants: Int = 0
)

case class PermutedBlock(
    nClausesAssertions: Int,
    nClausesLoopInvariants: Int,
    opList: List[IRGraph.Op]
)

case class PermutedPredicate(
    predicate: IRGraph.Predicate,
    nClauses: Int
)

case class PermutedOp(
    nClausesAssertions: Int = 0,
    nCLausesLoopInvariants: Int = 0,
    op: Option[IRGraph.Op] = None
)
object PermuteMode extends Enumeration {
  type PermuteMode = Value
  val Exp, Linear, Append = Value
}
object PermuteTarget extends Enumeration {
  type PermuteTarget = Value
  val Expr, Predicate, Field, Fold, Assert, All = Value
}

abstract class Permuter[T, S]() {
  final var contents: ListBuffer[ListBuffer[T]] = ListBuffer()
  private final def permuteExp(toPermute: List[S]): Unit = {
    val permutationsToAppend: ListBuffer[ListBuffer[T]] = ListBuffer();
    toPermute.foreach(item => {
      permutationsToAppend ++= contents.map(linearLayer => {
        linearLayer.map(marker => {
          combine(marker, item)
        })
      })
    })
    contents ++= permutationsToAppend
  }

  private final def permuteLinear(toPermute: List[S]): Unit = {
    val lastLinear = contents.last
    toPermute.foreach(item => {
      contents += lastLinear.map(marker => {
        combine(marker, item)
      })
    })
  }

  private final def append(toAppend: List[S]): Unit = {
    toAppend.foreach(item => {
      contents = contents.map(linear => {
        linear.map(append => {
          combine(append, item)
        })
      })
    })
  }
  final def permute(
      toPermute: S,
      modeMap: Map[PermuteTarget, PermuteMode]
  ): Unit = {
    permute(List(toPermute), modeMap);
  }
  final def permute(
      toPermute: List[S],
      modeMap: Map[PermuteTarget, PermuteMode]
  ): Unit = {
    if (toPermute.nonEmpty) {
      getPermuteMode(toPermute.last, modeMap) match {
        case gvc.visualizer.PermuteMode.Exp    => permuteExp(toPermute)
        case gvc.visualizer.PermuteMode.Linear => permuteLinear(toPermute)
        case gvc.visualizer.PermuteMode.Append => append(toPermute)
      }
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
      if (toAppend.op.isDefined)
        root.opList.map(_.copy) ++ List(toAppend.op.get)
      else root.opList.map(_.copy)
    )
  }

  override def getPermuteMode(
      toPermute: PermutedOp,
      modeMap: Map[PermuteTarget, PermuteMode]
  ): PermuteMode = {
    if (toPermute.op.isDefined) {
      toPermute.op.get match {
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            modeMap.getOrElse(PermuteTarget.Fold, PermuteMode.Linear)
          } else {
            Append
          }
        case _: IRGraph.Fold =>
          modeMap.getOrElse(PermuteTarget.Fold, PermuteMode.Linear)
        case _: IRGraph.Unfold =>
          modeMap.getOrElse(PermuteTarget.Fold, PermuteMode.Linear)
        case _ => Append
      }
    } else {
      Append
    }
  }
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
          case None => root
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
