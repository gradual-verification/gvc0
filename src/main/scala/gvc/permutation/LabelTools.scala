package gvc.permutation
import gvc.permutation.SamplingHeuristic.SamplingHeuristic

import scala.collection.mutable
object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

class Sampler {
  util.Random.setSeed(41L)
  private val prevSamples: mutable.Set[Int] = mutable.Set[Int]()
  def sample(
      list: List[ASTLabel],
      heuristic: SamplingHeuristic
  ): List[ASTLabel] = {
    heuristic match {
      case SamplingHeuristic.Random =>
        var sampled = sampleRandom(list)
        var hashCode = LabelTools.hashPermutation(sampled).hashCode
        while (prevSamples.contains(hashCode)) {
          sampled = sampleRandom(list)
          hashCode = LabelTools.hashPermutation(sampled).hashCode
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

  def hashPermutation(labels: List[ASTLabel]): String = {
    labels.foldLeft("")(_ + _.hash + " | ")
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
