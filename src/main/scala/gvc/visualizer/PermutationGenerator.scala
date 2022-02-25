package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Block, Expression, Method, Predicate, Program}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.Labeller.ASTLabel
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

object Labeller {

  case class ASTOffset(labels: List[ASTLabel], offset: Int)

  def labelAST(program: Program): List[ASTLabel] = {
    val methodLabels = program.methods.flatMap(labelMethod)
    val predicateLabels = program.predicates.flatMap(labelPredicate)
    (methodLabels ++ predicateLabels).toList
  }

  class PermutationException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }

  private def fact(n: Int): Int = if (n == 0) 1 else n * fact(n - 1)

  private def labelPredicate(predicate: Predicate): List[ASTLabel] = {
    labelExpression(
      Right(predicate),
      SpecType.Predicate,
      Some(predicate.expression)
    ).labels
  }

  private def labelMethod(method: Method): List[ASTLabel] = {
    labelBlock(method, method.body).labels
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
            offset = specAssertOffset.offset
            astLabelBuffer += specAssertOffset.labels
          }
        case _: IRGraph.Fold =>
          astLabelBuffer += ASTLabel(
            Left(context),
            SpecType.Fold,
            ExprType.Predicate,
            offset
          )
          offset += 1
        case _: IRGraph.Unfold =>
          astLabelBuffer += ASTLabel(
            Left(context),
            SpecType.Unfold,
            ExprType.Predicate,
            offset
          )
          offset += 1
        case ifstmt: IRGraph.If =>
          val trueBranchOffset = labelBlock(context, ifstmt.ifTrue, offset)
          val falseBranchOffset =
            labelBlock(context, ifstmt.ifFalse, trueBranchOffset.offset)
          offset = falseBranchOffset.offset
          astLabelBuffer += trueBranchOffset.labels ++ falseBranchOffset.labels
        case whl: IRGraph.While =>
          val invariantOffset =
            labelExpression(
              Left(context),
              SpecType.Invariant,
              whl.invariant,
              offset
            )
          val whlBlockOffset =
            labelBlock(context, whl.body, invariantOffset.offset)
          offset = whlBlockOffset.offset
          astLabelBuffer += invariantOffset.labels ++ whlBlockOffset.labels
        case _ =>
      }
    }
    ASTOffset(astLabelBuffer.toList, offset)
  }

  private def labelExpression(
      context: Either[Method, Predicate],
      specType: SpecType,
      expression: Option[Expression],
      baseIndex: Int = 0
  ): ASTOffset = {

    expression match {
      case Some(expr) =>
        val astLabelBuffer = ListBuffer()
        val exprStack = ListBuffer(expr)
        var offset = baseIndex
        while (exprStack.nonEmpty) {
          val top = exprStack.remove(exprStack.length - 1)
          top match {
            case _: IRGraph.Accessibility =>
              astLabelBuffer += ASTLabel(
                context,
                specType,
                ExprType.Accessibility,
                offset
              )
              offset += 1
            case _: IRGraph.PredicateInstance =>
              astLabelBuffer += ASTLabel(
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
            case conditional: IRGraph.Conditional => {
              val trueBranchOffset = labelExpression(
                context,
                specType,
                Some(conditional.ifTrue),
                offset
              )
              val falseBranchOffset = labelExpression(
                context,
                specType,
                Some(conditional.ifFalse),
                trueBranchOffset.offset
              )
              offset = falseBranchOffset.offset
              astLabelBuffer += trueBranchOffset.labels ++ falseBranchOffset.labels
            }
            case binary: IRGraph.Binary =>
              if (binary.operator == IRGraph.BinaryOp.And) {
                exprStack += binary.left
                exprStack += binary.right
              } else {
                ASTLabel(context, specType, ExprType.Default, offset)
              }
            case _ => ASTLabel(context, specType, ExprType.Default, offset)
          }
        }
        ASTOffset(astLabelBuffer.toList, offset)
      case None => ASTOffset(List.empty, baseIndex)
    }
  }
  def sample(
      list: List[ASTLabel],
      heuristic: SamplingHeuristic,
      nSamples: Int = 1
  ): List[List[ASTLabel]] = {
    heuristic match {
      case SamplingHeuristic.Random =>
        sampleRandom(list, nSamples)
      case SamplingHeuristic.None =>
        sampleAll(list)
      case _ => throw new PermutationException("Invalid sampling heuristic.")
    }
  }

  private def sampleRandom(
      orderedList: List[ASTLabel],
      nUniqueSamples: Int
  ): List[List[ASTLabel]] = {
    if (nUniqueSamples > fact(orderedList.length)) {
      throw new PermutationException(
        "Requested number of random samples exceeds n!."
      )
    } else {
      val permutationBuffer: ListBuffer[List[ASTLabel]] = ListBuffer.empty
      var prevShuffle = scala.util.Random.shuffle(orderedList.indices.toList)
      val idSet = mutable.Set[String]()
      while (permutationBuffer.length < nUniqueSamples) {
        val nextPermutation = prevShuffle.map(index => orderedList(index))
        val permutationHash = hashList(nextPermutation)
        if (!idSet.contains(permutationHash))
          permutationBuffer += nextPermutation
        prevShuffle = scala.util.Random.shuffle(prevShuffle)
      }
      permutationBuffer.toList
    }
  }

  private def sampleAll(orderedList: List[ASTLabel]): List[List[ASTLabel]] = ???

  case class ASTLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType,
      expressionIndex: Int
  )

  def hashList(labelList: List[ASTLabel]): String = {
    val sb = new StringBuilder
    for (b <- labelList.flatMap(hashLabel(_))) {
      sb.append(String.format("%02x", Byte.box(b)))
    }
    sb.toString
  }

  def hashLabel(label: ASTLabel): Array[Byte] = {
    val name = label.parent match {
      case Left(value)  => "m." + value.name
      case Right(value) => "p." + value.name
    }
    val representation =
      name + '.' + label.specType.id + '.' + label.expressionIndex + '.'
    representation.getBytes()
  }
}

object PermutationGenerator {
  def permute(
      program: Program,
      samplingHeuristic: SamplingHeuristic,
      nPermutations: Int = 1
  ): List[Program] = {
    val labels = Labeller.labelAST(program)
    val permutations =
      Labeller.sample(labels, samplingHeuristic, nPermutations)
    permutations.flatMap(perm => {
      (0 to perm.length).map(index => {
        generatePermutation(labels.slice(0, index).toSet)
      })
    })
  }
  def generatePermutation(labels: Set[ASTLabel]): Program = {
    new Program()
  }
  def buildPredicate(relevantLabels: Set[ASTLabel]): PermutedPredicate = ???
  def buildMethod(relevantLabels: Set[ASTLabel]): PermutedMethod = ???
  def buildBlock(relevantLabels: Set[ASTLabel]): PermutedBlock = ???
  def buildExpression(relevantLabels: Set[ASTLabel]): PermutedExpression = ???
}
