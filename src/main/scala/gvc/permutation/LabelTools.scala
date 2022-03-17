package gvc.permutation
import gvc.permutation.SamplingHeuristic.SamplingHeuristic
object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

object LabelTools {

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
    util.Random.setSeed(41L)
    val shuffle = scala.util.Random.shuffle(orderedList.indices.toList)
    shuffle.map(index => orderedList(index))
  }

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
