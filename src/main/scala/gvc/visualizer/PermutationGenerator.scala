package gvc.visualizer
import gvc.transformer.IRGraph.{Method, Predicate, Program}
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic

import scala.collection.mutable.ListBuffer

object SpecType extends Enumeration {
  type SpecType = Value
  val Assert, Precondition, Postcondition, Fold, Unfold, Invariant = Value
}
object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random = Value
}
object Labeller {
  def labelAST(program: Program): List[ASTLabel] = {
    val methodLabels = program.methods.flatMap(labelMethod(_))
    val predicateLabels = program.predicates.flatMap(labelPredicate(_))
    (methodLabels ++ predicateLabels).toList
  }
  class PermutationException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }
  private def fact(n: Int): Int = if (n == 0) 1 else n * fact(n - 1)

  private def labelPredicate(predicate: Predicate): List[ASTLabel] = {
    List()
  }
  private def labelMethod(method: Method): List[ASTLabel] = {
    List()
  }
  private def labelBlock(predicate: Predicate): List[ASTLabel] = {
    List()
  }
  private def labelExpression(
      context: Either[Method, Predicate]
  ): List[ASTLabel] = {
    List()
  }
  def sample(
      list: List[ASTLabel],
      nSamples: Int,
      heuristic: SamplingHeuristic
  ): List[List[ASTLabel]] = {
    heuristic match {
      case gvc.visualizer.SamplingHeuristic.Random =>
        randomSample(list, nSamples)
      case _ => throw new PermutationException("Invalid sampling heuristic.")
    }
  }
  private def randomSample(
      orderedList: List[ASTLabel],
      nSamples: Int
  ): List[List[ASTLabel]] = {
    if (nSamples > fact(orderedList.length)) {
      throw new PermutationException(
        "Requested number of random samples exceeds n!."
      )
    } else {
      val permutationBuffer: ListBuffer[List[ASTLabel]] = ListBuffer.empty
      var prevShuffle = scala.util.Random.shuffle(orderedList.indices.toList)
      while (permutationBuffer.length < nSamples) {
        permutationBuffer += prevShuffle.map(index => orderedList(index)).toList
        prevShuffle = scala.util.Random.shuffle(prevShuffle)
      }
      permutationBuffer.toList
    }
  }
  case class ASTLabel(
      parent: Either[Method, Predicate],
      expressionOrder: Int
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
      name + '.' + label.expressionOrder
    representation.getBytes()
  }
}
object PermutationGenerator {
  def permute(
      program: Program,
      nPermutations: Int,
      samplingHeuristic: SamplingHeuristic
  ): List[Program] = {
    val labels = Labeller.labelAST(program)
    val permutations =
      Labeller.sample(labels, nPermutations, samplingHeuristic)
    permutations.flatMap(perm => {
      (0 to perm.length).map(index => {
        generatePermutation(labels.slice(0, index).toSet)
      })
    })
  }
  def generatePermutation(labels: Set[ASTLabel]): Program = {
    new Program()
  }
  def buildPredicate(relevantLabels: Set[ASTLabel]): PermutedPredicate = {}
  def buildMethod(relevantLabels: Set[ASTLabel]): PermutedMethod = {}
  def buildBlock(relevantLabels: Set[ASTLabel]): PermutedBlock
  def buildExpression(relevantLabels: Set[ASTLabel]): PermutedExpression = {}
}
