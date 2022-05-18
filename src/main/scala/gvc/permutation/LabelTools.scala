package gvc.permutation
import gvc.permutation.Bench.BenchmarkException
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.SamplingHeuristic.SamplingHeuristic
import gvc.transformer.IR.{Expression, Method}

import java.math.BigInteger
import scala.collection.mutable
object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}
case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

class Sampler(benchConfig: BenchmarkConfig) {
  util.Random.setSeed(41L)
  private val prevSamples: mutable.Set[BigInteger] =
    mutable.Set[BigInteger]()
  def sample(
      heuristic: SamplingHeuristic
  ): List[ASTLabel] = {
    heuristic match {
      case SamplingHeuristic.Random =>
        var sampled = sampleRandom(benchConfig.labelOutput.labels)
        var hashCode =
          LabelTools.hashPath(benchConfig.labelOutput.labels, sampled)
        while (prevSamples.contains(hashCode)) {
          sampled = sampleRandom(benchConfig.labelOutput.labels)
          hashCode =
            LabelTools.hashPath(benchConfig.labelOutput.labels, sampled)
        }
        prevSamples += hashCode
        sampled
      case _ => throw new LabelException("Invalid sampling heuristic.")
    }
  }
  private def sampleRandom(
      orderedList: List[ASTLabel]
  ): List[ASTLabel] = scala.util.Random.shuffle(orderedList)
}

object LabelTools {
  val hexRegex = "[0-9A-Fa-f]+"

  def hashPath(
      template: List[ASTLabel],
      labels: List[ASTLabel]
  ): BigInteger = {
    val hash =
      labels.map(template.indexOf(_).toHexString).foldLeft("")(_ + _)
    new BigInteger(hash, 16)
  }

  def parseID(input: String): Option[BigInteger] = {
    if (input.matches("[0-9A-Fa-f]+")) {
      Some(new BigInteger(input, 16))
    } else {
      None
    }
  }

  def appendPathComment(
      str: String,
      labels: List[ASTLabel]
  ): String = {
    "/*\n" +
      labels.foldLeft("")(_ + _.hash + '\n') +
      "*/\n" +
      str
  }
}

class LabelPermutation(
    benchmarkConfig: BenchmarkConfig
) {
  private val contents = mutable.TreeSet[ASTLabel]()(LabelOrdering)
  private val orderedIndices = mutable.ListBuffer[Int]()
  private val foldUnfoldCounts = mutable.Map[Method, Int]()
  private val completedImpreciseExpressions = mutable.Set[Int]()
  private var completedExpressions = mutable.Set[Int]()
  def addLabel(label: ASTLabel): Unit = {
    orderedIndices += label.exprIndex
    contents += label
    label.parent match {
      case Left(value) =>
        label.specType match {
          case gvc.permutation.SpecType.Fold |
              gvc.permutation.SpecType.Unfold =>
            if (foldUnfoldCounts.contains(value))
              foldUnfoldCounts(value) += 1
            else foldUnfoldCounts += value -> 1
          case _ =>
        }
      case Right(_) =>
    }
  }
  def labels: Set[ASTLabel] = contents.toSet
  def indices: Set[Int] = orderedIndices.toSet

  def imprecisionStatusList: List[Int] = {
    benchmarkConfig.labelOutput.specsToSpecIndices.values.toList.sorted
      .map(index => {
        (if (completedExpressions.contains(index)) 1 else 0)
      })
  }

  def specStatusList: List[Int] = {
    benchmarkConfig.labelOutput.labels
      .map(label => {
        (if (labels.contains(label)) 1 else 0)
      })
  }

  def exprIsComplete(template: Expression, componentCount: Int): Boolean = {
    val condition = benchmarkConfig.labelOutput.specsToSpecIndices
      .contains(template) && benchmarkConfig.labelOutput.labelsPerSpecIndex(
      benchmarkConfig.labelOutput
        .specsToSpecIndices(template)) == componentCount

    if (!benchmarkConfig.labelOutput.specsToSpecIndices.contains(template)) {
      throw new BenchmarkException(
        "Cannot generate permutations of an expression that wasn't present in the original compiled IR.")
    }

    val templateIndex =
      benchmarkConfig.labelOutput.specsToSpecIndices(template)

    if (condition) {
      if (completedImpreciseExpressions.contains(templateIndex)) {
        completedImpreciseExpressions.remove(templateIndex)
        completedExpressions += templateIndex
        false
      } else if (completedExpressions.contains(templateIndex)) {
        true
      } else {
        completedImpreciseExpressions += templateIndex
        false
      }
    } else {
      false
    }
  }

  def methodIsComplete(method: Method): Boolean = {
    this.benchmarkConfig.labelOutput
      .foldUnfoldCount(method) == 0 || (this.foldUnfoldCounts
      .contains(method) &&
    this.foldUnfoldCounts(method) == this.benchmarkConfig.labelOutput
      .foldUnfoldCount(method))
  }

  def markAllComplete(): Unit = {
    completedExpressions =
      completedExpressions.union(completedImpreciseExpressions)
  }

  def id: BigInteger = {
    val specsPresent = specStatusList.foldRight("")(_.toString + _)
    val imprecisionPresent = imprecisionStatusList.foldRight("")(_.toString + _)
    new BigInteger(
      specsPresent + imprecisionPresent,
      2
    )
  }
}

class LabelException(str: String) extends Exception(str)
