package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate, Program}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic
import gvc.visualizer.SpecType.SpecType
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

object Labeller {

  case class ASTOffset(labels: List[ASTLabel])

  def labelAST(program: Program): List[ASTLabel] = {
    val methodLabels = program.methods.flatMap(labelMethod)
    val predicateLabels = program.predicates.flatMap(labelPredicate)
    val totalLabels = (methodLabels ++ predicateLabels).toList
    if (totalLabels.isEmpty)
      throw new LabelException(
        "Program doesn't contain any specifications to permute."
      )
    totalLabels
  }

  class LabelException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def labelPredicate(predicate: Predicate): List[ASTLabel] = {
    labelExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression)
    ).labels
  }

  private def labelMethod(method: Method): List[ASTLabel] = {
    val precondition =
      labelExpression(Left(method), SpecType.Precondition, method.precondition)
    val postcondition =
      labelExpression(
        Left(method),
        SpecType.Postcondition,
        method.postcondition,
        precondition.labels.length
      )
    precondition.labels ++ postcondition.labels ++ labelBlock(
      method,
      method.body,
      postcondition.labels.length + precondition.labels.length
    ).labels
  }

  private def labelBlock(
      context: Method,
      block: Block,
      baseIndex: Int = 0
  ): ASTOffset = {
    val astLabelBuffer: ListBuffer[ASTLabel] = ListBuffer()
    var offset = baseIndex
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            val specAssertOffset =
              labelExpression(
                Left(context),
                SpecType.Assert,
                Some(assert.value),
                offset
              )
            offset += specAssertOffset.labels.length
            astLabelBuffer ++= specAssertOffset.labels
          }
        case _: IRGraph.Fold =>
          astLabelBuffer += createLabel(
            Left(context),
            SpecType.Fold,
            ExprType.Predicate,
            offset
          )
          offset += 1
        case _: IRGraph.Unfold =>
          astLabelBuffer += createLabel(
            Left(context),
            SpecType.Unfold,
            ExprType.Predicate,
            offset
          )
          offset += 1
        case ifstmt: IRGraph.If =>
          val trueBranchOffset = labelBlock(context, ifstmt.ifTrue, offset)
          offset += trueBranchOffset.labels.length

          val falseBranchOffset =
            labelBlock(
              context,
              ifstmt.ifFalse,
              offset + trueBranchOffset.labels.length
            )
          offset += falseBranchOffset.labels.length

          astLabelBuffer ++= trueBranchOffset.labels ++ falseBranchOffset.labels
        case whl: IRGraph.While =>
          val invariantOffset =
            labelExpression(
              Left(context),
              SpecType.Invariant,
              whl.invariant,
              offset
            )
          offset += invariantOffset.labels.length
          val whlBlockOffset =
            labelBlock(context, whl.body, offset)
          offset += whlBlockOffset.labels.length
          astLabelBuffer ++= invariantOffset.labels ++ whlBlockOffset.labels
        case _ =>
      }
    }
    ASTOffset(astLabelBuffer.toList)
  }

  private def labelExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      baseIndex: Int = 0
  ): ASTOffset = {

    expression match {
      case Some(expr) =>
        val astLabelBuffer: ListBuffer[ASTLabel] = ListBuffer()
        val exprStack = ListBuffer(expr)
        var offset = baseIndex
        while (exprStack.nonEmpty) {
          val top = exprStack.remove(exprStack.length - 1)
          top match {
            case _: IRGraph.Accessibility =>
              astLabelBuffer += createLabel(
                context,
                specType,
                ExprType.Accessibility,
                offset
              )
              offset += 1
            case _: IRGraph.PredicateInstance =>
              astLabelBuffer += createLabel(
                context,
                specType,
                ExprType.Predicate,
                offset
              )
              offset += 1
            case imprecise: IRGraph.Imprecise =>
              labelExpression(
                context,
                specType,
                imprecise.precise,
                baseIndex
              )
            case conditional: IRGraph.Conditional =>
              val trueBranchOffset = labelExpression(
                context,
                specType,
                Some(conditional.ifTrue),
                offset
              )
              offset += trueBranchOffset.labels.length

              val falseBranchOffset = labelExpression(
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
                createLabel(context, specType, ExprType.Default, offset)
              }
            case _ => createLabel(context, specType, ExprType.Default, offset)
          }
        }
        ASTOffset(astLabelBuffer.toList)
      case None => ASTOffset(List.empty)
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

  case class ASTLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int,
      hash: String
  )
  object LabelOrdering extends Ordering[ASTLabel] {
    override def compare(
        x: ASTLabel,
        y: ASTLabel
    ): Int =
      (x.parent.hashCode() compare y.parent
        .hashCode()) compare (x.expressionIndex compare y.expressionIndex)
  }

  def createLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int
  ): ASTLabel = {
    val name = parent match {
      case Left(value)  => "m." + value.name
      case Right(value) => "p." + value.name
    }
    val hash =
      name + '.' + specType.id + '.' + expressionIndex + '.' + (specType match {
        case SpecType.Postcondition => "postcondition"
        case SpecType.Assert        => "assert"
        case SpecType.Precondition  => "precondition"
        case SpecType.Unfold        => "unfold"
        case SpecType.Fold          => "fold"
        case SpecType.Predicate     => "predicate"
        case SpecType.Invariant     => "invariant"
      })

    ASTLabel(parent, specType, exprType, expressionIndex, hash)
  }

  case class LabelMeta(
      nClausesAssertions: Int,
      nClausesPreconditions: Int,
      nClausesPostconditions: Int,
      nClausesLoopInvariants: Int,
      nClausesPredicates: Int,
      nFolds: Int,
      nUnfolds: Int
  )
  def sampleMetadata(list: List[ASTLabel]): LabelMeta = {
    var nClausesAssertions: Int = 0
    var nClausesPreconditions: Int = 0
    var nClausesPostconditions: Int = 0
    var nClausesLoopInvariants: Int = 0
    var nClausesPredicates: Int = 0
    var nFolds: Int = 0
    var nUnfolds: Int = 0

    list.foreach(label => {
      label.specType match {
        case gvc.visualizer.SpecType.Assert       => nClausesAssertions += 1
        case gvc.visualizer.SpecType.Precondition => nClausesPreconditions += 1
        case gvc.visualizer.SpecType.Postcondition =>
          nClausesPostconditions += 1
        case gvc.visualizer.SpecType.Fold      => nFolds += 1
        case gvc.visualizer.SpecType.Unfold    => nUnfolds += 1
        case gvc.visualizer.SpecType.Invariant => nClausesLoopInvariants += 1
        case gvc.visualizer.SpecType.Predicate => nClausesPredicates += 1
      }
    })
    LabelMeta(
      nClausesAssertions,
      nClausesPreconditions,
      nClausesPostconditions,
      nClausesLoopInvariants,
      nClausesPredicates,
      nFolds,
      nUnfolds
    )
  }
}
