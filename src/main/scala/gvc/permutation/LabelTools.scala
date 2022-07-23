package gvc.permutation

import gvc.permutation.Bench.BenchmarkException
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.SamplingHeuristic.SamplingHeuristic
import gvc.transformer.IR.{Expression, Method, Predicate}

import java.math.BigInteger
import scala.collection.mutable

object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

class Sampler(benchConfig: BenchmarkConfig) {
  private val rng = new scala.util.Random
  rng.setSeed(41141441)
  private val prevSamples: mutable.Set[BigInteger] =
    mutable.Set[BigInteger]()

  def numSampled: Int = prevSamples.size

  private val specImprecisionLabels = benchConfig.labelOutput.labels
    .filter(p => p.exprType == ExprType.Imprecision)
    .map(label => {
      label.specIndex -> label
    })
    .toMap
  private val componentLabels =
    benchConfig.labelOutput.labels.toSet
      .diff(specImprecisionLabels.values.toSet)
      .filter(p => p.exprType != ExprType.Absent)
      .toList

  case class ImprecisionRemovalPoint(specIndex: Int, insertionIndex: Int)

  def findInsertionPoints(
      listOfComponents: List[ASTLabel]
  ): Map[Int, Int] = {
    val lastComponentWithSpecIndexAt = mutable.Map[Int, Int]()
    val lastFoldUnfoldForMethod = mutable.Map[Method, Int]()
    val specIndexToContext = mutable.Map[Int, Either[Method, Predicate]]()
    for (index <- listOfComponents.indices) {
      val label = listOfComponents(index)
      label.specType match {
        case gvc.permutation.SpecType.Fold | gvc.permutation.SpecType.Unfold =>
          label.parent match {
            case Left(method) => lastFoldUnfoldForMethod += (method -> index)
            case Right(pred) =>
              throw new BenchmarkException(
                s"A fold or unfold was associated with the body of the predicate ${pred.name}")
          }
        case gvc.permutation.SpecType.Assert =>
        case _ =>
          specIndexToContext += (label.specIndex -> label.parent)
          lastComponentWithSpecIndexAt += (label.specIndex -> index)
      }
    }
    lastComponentWithSpecIndexAt
      .map(pair => {
        val context = specIndexToContext(pair._1)
        val firstValidIndex = context match {
          case Left(value) =>
            val methodCompletedAt = lastFoldUnfoldForMethod.getOrElse(value, 0)
            math.max(pair._2, methodCompletedAt)
          case Right(_) => pair._2
        }
        val randomOffset: Int = this.rng.nextInt(
          Math.floor(listOfComponents.length - firstValidIndex).toInt) + 1
        (pair._1, firstValidIndex + randomOffset)
      })
      .toMap
  }

  def sample(
      heuristic: SamplingHeuristic
  ): List[ASTLabel] = {
    def getSample: List[ASTLabel] = {
      val sampled = heuristic match {
        case SamplingHeuristic.Random => sampleRandom
        case _                        => throw new LabelException("Invalid sampling heuristic.")
      }
      if (sampled.size != benchConfig.labelOutput.labels.size) {
        throw new BenchmarkException(
          "Size of permutation doesn't match size of template.")
      }
      sampled
    }

    var sampled = getSample
    var hashCode =
      LabelTools.hashPath(benchConfig.labelOutput.labels, sampled)
    while (prevSamples.contains(hashCode)) {
      sampled = getSample
      hashCode = LabelTools.hashPath(benchConfig.labelOutput.labels, sampled)
    }
    prevSamples += hashCode
    sampled
  }

  private def sampleRandom: List[ASTLabel] = {
    val sample = mutable.ListBuffer.empty ++ this.rng
      .shuffle(this.componentLabels)
    val pointMapping = findInsertionPoints(sample.toList)
    val sortedTuples = pointMapping.toList
      .sortWith((pair1, pair2) => {
        pair1._2 < pair2._2
      })
      .zipWithIndex
    sortedTuples.foreach(point => {
      sample.insert(point._1._2 + point._2, specImprecisionLabels(point._1._1))
    })
    sample.toList
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
  private val contents = mutable.ListBuffer[ASTLabel]()
  private val orderedIndices = mutable.ListBuffer[Int]()
  private val foldUnfoldCounts = mutable.Map[Method, Int]()
  val completedExpressions = mutable.Set[Int]()

  def addLabel(label: ASTLabel): Unit = {
    orderedIndices += label.exprIndex
    contents += label
    label.parent match {
      case Left(value) =>
        label.specType match {
          case gvc.permutation.SpecType.Fold |
              gvc.permutation.SpecType.Unfold =>
            foldUnfoldCounts += value -> (foldUnfoldCounts.getOrElse(value, 0) + 1)
          case _ =>
        }
      case Right(_) =>
    }
    label.exprType match {
      case gvc.permutation.ExprType.Imprecision =>
        completedExpressions += label.specIndex
      case _ =>
    }
  }

  def labels: List[ASTLabel] = contents.toList.sorted(LabelOrdering)

  def indices: Set[Int] = orderedIndices.toSet

  def imprecisionStatusList: List[Int] = {
    benchmarkConfig.labelOutput.specsToSpecIndices.values.toList.sorted
      .map(index => {
        if (completedExpressions.contains(index)) 1 else 0
      })
  }

  def specStatusList: List[Int] = {
    benchmarkConfig.labelOutput.labels
      .map(label => {
        if (labels.contains(label)) 1 else 0
      })
  }

  def exprIsComplete(template: Expression): Boolean =
    completedExpressions.nonEmpty &&
      benchmarkConfig.labelOutput.specsToSpecIndices
        .contains(template) && completedExpressions.contains(
      benchmarkConfig.labelOutput.specsToSpecIndices(template))

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
