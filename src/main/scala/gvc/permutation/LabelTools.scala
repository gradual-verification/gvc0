package gvc.permutation
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.SamplingHeuristic.SamplingHeuristic
import gvc.transformer.IR.{Method, Predicate}

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
    val shuffle = scala.util.Random.shuffle(orderedList.indices.toList)
    shuffle.map(index => orderedList(index))
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
  private val methodLabelCounts = mutable.Map[String, Int]()
  private val predicateLabelCounts = mutable.Map[String, Int]()
  private val orderedContents = mutable.TreeSet[ASTLabel]()(LabelOrdering)
  private val orderedIndices = mutable.ListBuffer[Int]()

  def addLabel(label: ASTLabel): Unit = {
    orderedIndices += label.exprIndex
    orderedContents += label
    label.parent match {
      case Left(value) => {
        if (!methodLabelCounts.contains(value.name)) {
          methodLabelCounts += (value.name -> 1)
        } else {
          methodLabelCounts(value.name) += 1
        }
        if (
          methodLabelCounts(
            value.name
          ) == benchmarkConfig.labelOutput.completeMethodCounts.getOrElse(
            value.name,
            0
          )
        ) {
          completedMethods += value.name
          updateFinishedMethod()

        }
      }
      case Right(value) =>
        if (!predicateLabelCounts.contains(value.name)) {
          predicateLabelCounts += (value.name -> 1)
        } else {
          predicateLabelCounts(value.name) += 1
        }
        if (
          predicateLabelCounts(
            value.name
          ) == benchmarkConfig.labelOutput.completePredicateCounts.getOrElse(
            value.name,
            0
          )
        ) {
          completedPredicates += value.name
          updateFinishedPredicate()

        }
    }
  }

  def labels: Set[ASTLabel] = orderedContents.toSet
  def indices: Set[Int] = orderedIndices.toSet

  val completedMethods: mutable.Set[String] = mutable.Set.empty[String]
  val completedPredicates: mutable.Set[String] = mutable.Set.empty[String]
  val finishedMethods: mutable.Set[String] = mutable.Set.empty[String]
  val finishedPredicates: mutable.Set[String] = mutable.Set.empty[String]

  def updateFinishedMethod(): Unit = {
    benchmarkConfig.labelOutput.methodPredicateDependencies.foreach(pair => {
      if (
        !finishedMethods.contains(pair._1) && completedMethods.contains(pair._1)
      ) {
        if (pair._2.diff(completedPredicates).isEmpty) {
          finishedMethods += pair._1
        }
      }
    })
  }

  def updateFinishedPredicate(): Unit = {
    benchmarkConfig.labelOutput.predicatePredicateDependencies.foreach(pair => {
      if (
        !finishedPredicates.contains(pair._1) && completedPredicates
          .contains(pair._1)
      ) {
        if (pair._2.diff(completedPredicates).isEmpty) {
          finishedPredicates += pair._1
        }
      }
    })
    updateFinishedMethod()
  }
  def methodIsFinished(method: Method): Boolean =
    finishedMethods.contains(method.name)
  def predicateIsFinished(predicate: Predicate): Boolean = {
    finishedPredicates.contains(predicate.name)
  }
}

class LabelException(str: String) extends Exception(str)
