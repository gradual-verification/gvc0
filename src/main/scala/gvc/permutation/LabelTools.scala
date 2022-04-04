package gvc.permutation
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.SamplingHeuristic.SamplingHeuristic

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
        var sampled = sampleRandom(benchConfig.labels)
        var hashCode = LabelTools.hashPermutation(benchConfig.labels, sampled)
        while (prevSamples.contains(hashCode)) {
          sampled = sampleRandom(benchConfig.labels)
          hashCode = LabelTools.hashPermutation(benchConfig.labels, sampled)
        }
        prevSamples += hashCode
        sampled
      case _ => throw new LabelException("Invalid sampling heuristic.")
    }
  }
  private def sampleRandom(
      orderedList: List[ASTLabel]
  ): List[ASTLabel] = {
    val shuffle = scala.util.Random.shuffle(orderedList.indices.toList)
    shuffle.map(index => orderedList(index))
  }
}

object LabelTools {

  def hashPermutation(
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

class LabelException(str: String) extends Exception(str)
