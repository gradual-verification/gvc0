package gvc.permutation
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
    mutable.Set[BigInteger]().union(benchConfig.prior.visitedPaths)
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
  ): List[ASTLabel] = {
    scala.util.Random.shuffle(orderedList)
  }
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

  def createID(
      template: List[ASTLabel],
      permutation: Set[ASTLabel]
  ): BigInteger = {
    new BigInteger(
      template
        .map(label => {
          (if (permutation.contains(label)) 1 else 0).toString
        })
        .foldRight("")(_ + _),
      2
    )
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

  def exprIsComplete(template: Expression, componentCount: Int): Boolean =
    benchmarkConfig.labelOutput.specsToSpecIndices
      .contains(template) && benchmarkConfig.labelOutput.labelsPerSpecIndex(
      benchmarkConfig.labelOutput
        .specsToSpecIndices(template)) == componentCount

  def methodIsComplete(method: Method): Boolean = {
    this.benchmarkConfig.labelOutput
      .foldUnfoldCount(method) == 0 || (this.foldUnfoldCounts
      .contains(method) &&
    this.foldUnfoldCounts(method) == this.benchmarkConfig.labelOutput
      .foldUnfoldCount(method))
  }
}

class LabelException(str: String) extends Exception(str)
