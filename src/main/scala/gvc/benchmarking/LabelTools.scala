package gvc.benchmarking

import gvc.benchmarking.BenchmarkSequential.BenchmarkException
import gvc.benchmarking.SamplingHeuristic.SamplingHeuristic
import gvc.transformer.IR.{Expression, Method, Predicate}

import java.math.BigInteger

import scala.collection.mutable

object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

class Sampler(labelOutput: LabelOutput) {
  private val rng = new scala.util.Random
  rng.setSeed(41141441)
  private val prevSamples: mutable.Set[BigInteger] =
    mutable.Set[BigInteger]()

  def numSampled: Int = prevSamples.size

  private val specImprecisionLabels = labelOutput.labels
    .filter(p => p.exprType == ExprType.Imprecision)
    .map(label => {
      label.specIndex -> label
    })
    .toMap
  private val componentLabels =
    labelOutput.labels.toSet
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
        case gvc.benchmarking.SpecType.Fold |
            gvc.benchmarking.SpecType.Unfold =>
          label.parent match {
            case Left(method) => lastFoldUnfoldForMethod += (method -> index)
            case Right(pred) =>
              throw new BenchmarkException(
                s"A fold or unfold was associated with the body of the predicate ${pred.name}"
              )
          }
        case gvc.benchmarking.SpecType.Assert =>
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
      if (sampled.size != labelOutput.labels.size) {
        throw new BenchmarkException(
          "Size of permutation doesn't match size of template.")
      }
      sampled
    }

    var sampled = getSample
    var hashCode =
      LabelTools.hashPath(labelOutput.labels, sampled)
    while (prevSamples.contains(hashCode)) {
      sampled = getSample
      hashCode = LabelTools.hashPath(labelOutput.labels, sampled)
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

  def permutationIDToPermutation(labelOut: LabelOutput, id: String,
  ): LabelPermutation = {

    val perm = new LabelPermutation(labelOut)
    val labels = labelOut.labels

    val flags = new BigInteger(id, 16)
      .toString(2)
      .toCharArray
      .map(c => {
        c == '1'
      })

    val excluded = flags.slice(1, flags.length)
    excluded.indices
      .filter(i => excluded(i))
      .map(i => labels(i))
      .foreach(perm.addLabel)
    if (!perm.id.toString(16).equals(id)) {
      throw new BenchmarkException(
        "The generated program doesn't match the permutation's ID.")
    }

    perm
  }

  val hexRegex = "[0-9A-Fa-f]+"

  //N!
  def theoreticalMaxPaths(n: Int): BigInt = {
    var f: BigInt = 1
    for (i <- 1 to n) {
      f = f * i;
    }
    f
  }

  def hashPath(
      template: List[ASTLabel],
      labels: List[ASTLabel]
  ): BigInteger = {
    val hash =
      labels.map(template.indexOf(_).toHexString).foldLeft("")(_ + _)
    new BigInteger(hash, 16)
  }

  def parseID(input: String): Option[BigInteger] = {
    if (input.matches(hexRegex)) {
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
    labelOutput: LabelOutput
) {
  private val contents = mutable.ListBuffer[ASTLabel]()
  private val orderedIndices = mutable.ListBuffer[Int]()
  private val foldUnfoldCounts = mutable.Map[Method, Int]()
  val completedExpressions: mutable.Set[Int] = mutable.Set[Int]()

  def addLabel(label: ASTLabel): Unit = {
    orderedIndices += label.exprIndex
    contents += label
    label.parent match {
      case Left(value) =>
        label.specType match {
          case gvc.benchmarking.SpecType.Fold |
              gvc.benchmarking.SpecType.Unfold =>
            foldUnfoldCounts += value -> (foldUnfoldCounts.getOrElse(
              value,
              0
            ) + 1)
          case _ =>
        }
      case Right(_) =>
    }
    label.exprType match {
      case gvc.benchmarking.ExprType.Imprecision =>
        completedExpressions += label.specIndex
      case _ =>
    }
  }

  def labels: List[ASTLabel] = contents.toList.sorted(LabelOrdering)

  def indices: Set[Int] = orderedIndices.toSet

  def imprecisionStatusList: List[Int] = {
    labelOutput.specsToSpecIndices.values.toList.sorted
      .map(index => {
        if (completedExpressions.contains(index)) 1 else 0
      })
  }

  def specStatusList: List[Int] = {
    labelOutput.labels
      .map(label => {
        if (this.labels.contains(label)) 1 else 0
      })
  }

  def exprIsComplete(template: Expression): Boolean =
    completedExpressions.nonEmpty &&
      labelOutput.specsToSpecIndices
        .contains(template) && completedExpressions.contains(
      labelOutput.specsToSpecIndices(template)
    )

  def id: BigInteger = {
    val specsPresent = "1" + specStatusList.foldLeft("")(_ + _)
    val big = new BigInteger(
      specsPresent,
      2
    )
    big
  }
}

class LabelException(str: String) extends Exception(str)
