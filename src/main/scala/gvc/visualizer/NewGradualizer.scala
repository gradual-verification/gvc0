package gvc.visualizer

import gvc.transformer.IRGraph
import gvc.visualizer.PermuteBlockTarget.PermuteBlockTarget
import gvc.visualizer.PermuteMode.{Exp, Linear, Append, PermuteMode}
import gvc.visualizer.PermuteTarget.PermuteTarget

import scala.collection.mutable.ListBuffer

class NewGradualizer {}

object PermuteMode extends Enumeration {
  type PermuteMode = Value
  val Exp, Linear, Append = Value
}

object PermuteTarget extends Enumeration {
  type PermuteTarget = Value
  val Accessibility, Predicate, Default = Value

}
object PermuteExpressionTarget extends Enumeration {
  type PermuteExpressionTarget = Value
  val Accessibility, Predicate, Default = Value
}

object PermuteBlockTarget extends Enumeration {
  type PermuteBlockTarget = Value
  val Fold, Unfold, Assert, Invariant = Value
}

object PermuteMethodTarget extends Enumeration {
  type PermuteMethodTarget = Value
  val Precondition, Postcondition = Value
}

abstract class PermutationLayer[T, S](
    mode: PermuteMode,
    next: Either[ListBuffer[PermutationLayer[T, S]], ListBuffer[T]]
) {
  val below = next
  def permute(toAppend: S)

  def append(toAppend: S)
}

abstract class ExponentialPermutationLayer[T, S](
    next: Either[ListBuffer[PermutationLayer[T, S]], ListBuffer[T]]
) extends PermutationLayer[T, S](
      Linear,
      next
    ) {
  override def permute(toAppend: S): Unit =



abstract class LinearPermutationLayer[T, S](
    next: Either[ListBuffer[PermutationLayer[T, S]], ListBuffer[T]]
) extends PermutationLayer[T, S](
      Linear,
      next
    ) {
  override def permute(toAppend: S): Unit = ???

}

abstract class AppendLayer[T, S](
    next: ListBuffer[T],
    combine: (T, S) => T
) extends PermutationLayer[T, S](Append, Right(next).asInstanceOf[Either[ListBuffer[PermutationLayer[T, S]], ListBuffer[T]]]) {
  def permute(toAppend: S): Unit = {

  }
}






abstract class PermutationSet[T, S](options: Map[Enumeration, PermuteMode]) {
  val appendLayer = AppendLayer[T, S](ListBuffer())

  def combine(target: T, source: S)

  final def append(toAppend: S): Unit = {
    permList.foreach(combine(_, toAppend))
  }
}

class BlockPermutationSet(options: Map[PermuteBlockTarget, PermuteMode])
    extends PermutationSet[IRGraph.Block, IRGraph.Op](
      options.asInstanceOf[Map[Enumeration, PermuteMode]]
    ) {
  override def combine(current: IRGraph.Block, toAppend: IRGraph.Op): Unit = {
    current += toAppend.copy
  }

}

class ExpressionPermutationSet(options: Map[PermuteTarget, PermuteMode])
    extends PermutationSet[IRGraph.Expression, IRGraph.Expression](
      options.asInstanceOf[Map[Enumeration, PermuteMode]]
    ) {
  override def combine(
      target: IRGraph.Expression,
      source: IRGraph.Expression
  ): Unit = ???
}
