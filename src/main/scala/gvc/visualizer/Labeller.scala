package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate, Program}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic
import gvc.visualizer.SpecType.SpecType

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object SpecType extends Enumeration {
  type SpecType = Value
  val Assert, Precondition, Postcondition, Fold, Unfold, Invariant, Predicate =
    Value
}

object ExprType extends Enumeration {
  type ExprType = Any
  val Accessibility, Predicate, Default = Value
}

object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

object Labeller {

  def labelAST(program: Program): List[ASTLabel] = {
    val labels = mutable.ListBuffer[ASTLabel]()
    program.methods.foreach(method => {
      labelMethod(method, labels)
    })
    program.predicates.foreach(predicate => {
      labelPredicate(predicate, labels)
    })
    if (labels.isEmpty)
      throw new LabelException(
        "Program doesn't contain any specifications to permute."
      )
    labels.sorted(LabelOrdering).toList
  }

  class LabelException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def labelPredicate(predicate: Predicate, labels: mutable.ListBuffer[ASTLabel]): Unit = {
    labelExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression),
      labels
    )
  }

  private def labelMethod(method: Method, labels: mutable.ListBuffer[ASTLabel]): Unit = {
      labelExpression(Left(method), SpecType.Precondition, method.precondition, labels)
      labelExpression(
        Left(method),
        SpecType.Postcondition,
        method.postcondition,
        labels
      )
    labelBlock(
      method,
      method.body,
      labels
    )
  }

  private def labelBlock(
      context: Method,
      block: Block,
      labels: mutable.ListBuffer[ASTLabel]
                        ): Unit = {
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            labelExpression(
              Left(context),
              SpecType.Assert,
              Some(assert.value),
              labels
            )
          }
        case _: IRGraph.Fold =>
          labels += createLabel(
            Left(context),
            SpecType.Fold,
            ExprType.Predicate,
            labels.length
          )
        case _: IRGraph.Unfold =>
          labels += createLabel(
            Left(context),
            SpecType.Unfold,
            ExprType.Predicate,
            labels.length
          )
        case ifstmt: IRGraph.If =>
          labelBlock(context, ifstmt.ifTrue, labels)
          labelBlock(context, ifstmt.ifFalse, labels)
        case whl: IRGraph.While =>
          labelExpression(
              Left(context),
              SpecType.Invariant,
              whl.invariant,
              labels
            )
          labelBlock(context, whl.body, labels)
        case _ =>
      }
    }
  }

  private def labelExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      labels: mutable.ListBuffer[ASTLabel]
  ):Unit = {
    expression match {
      case Some(expr) =>
          expr match {
            case _: IRGraph.Accessibility =>
              labels += createLabel(
                context,
                specType,
                ExprType.Accessibility,
                labels.length
              )
            case _: IRGraph.PredicateInstance =>
              labels += createLabel(
                context,
                specType,
                ExprType.Predicate,
                labels.length
              )
            case imprecise: IRGraph.Imprecise =>
              labelExpression(
                context,
                specType,
                imprecise.precise,
                labels
              )
            case conditional: IRGraph.Conditional =>
              labelExpression(
                context,
                specType,
                Some(conditional.ifTrue),
                labels
              )
             labelExpression(
                context,
                specType,
                Some(conditional.ifFalse),
                labels
              )
            case binary: IRGraph.Binary =>
              if (binary.operator == IRGraph.BinaryOp.And) {
                labelExpression(context, specType, Some(binary.right), labels)
                labelExpression(context, specType, Some(binary.left), labels)
              } else {
                labels += createLabel(context, specType,exprType=ExprType.Default, labels.length)
              }
            case _ => labels += createLabel(context, specType, exprType=ExprType.Default, labels.length)
          }
      case None =>
    }
  }

  def sample(
      list: List[ASTLabel],
      heuristic: SamplingHeuristic
  ): List[ASTLabel] = {
    heuristic match {
      case SamplingHeuristic.Random =>
        sampleRandom(list)
      case _ => throw new LabelException("Invalid sampling heuristic.")
    }
  }

  private def sampleRandom(
      orderedList: List[ASTLabel]
  ): List[ASTLabel] = {
    val shuffle = scala.util.Random.shuffle(orderedList.indices.toList)
    shuffle.map(index => orderedList(index))

  }

  class ASTLabel(
      val parent: Either[Method, Predicate],
      val specType: SpecType,
      val exprType: ExprType,
      val exprIndex: Int,
                ) {
    val hash: String = {
      val name = parent match {
        case Left(value)  => "m." + value.name
        case Right(value) => "p." + value.name
      }
      name + '.' + specType.id + '.' + exprIndex + '.' + (specType match {
        case SpecType.Postcondition => "post"
        case SpecType.Assert        => "assert"
        case SpecType.Precondition  => "pre"
        case SpecType.Unfold        => "unfold"
        case SpecType.Fold          => "fold"
        case SpecType.Predicate     => "pred"
        case SpecType.Invariant     => "inv"
      })
    }
  }
  object LabelOrdering extends Ordering[ASTLabel] {
    override def compare(
        x: ASTLabel,
        y: ASTLabel
    ): Int =
      x.exprIndex compare y.exprIndex
  }

  def createLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int
  ): ASTLabel = {
    new ASTLabel(parent, specType, exprType, expressionIndex)
  }

  def hashPermutation(labels: List[ASTLabel]): String = {
    labels.foldLeft("")(_ + _.hash + " | ")
  }
}
