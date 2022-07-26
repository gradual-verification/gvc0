package gvc.benchmarking

import gvc.benchmarking.BenchmarkSequential.BenchmarkException
import gvc.benchmarking.SamplingHeuristic.SamplingHeuristic
import gvc.transformer.IR.{Expression, Method, Predicate}

import java.math.BigInteger
import java.nio.{ByteBuffer, ByteOrder}
import scala.collection.mutable

object SamplingHeuristic extends Enumeration {
  type SamplingHeuristic = Value
  val Random, None = Value
}

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

class Sampler(labelOutput: LabelOutput) {
  private val rng = new scala.util.Random
  rng.setSeed(41141441)
  private val prevSamples: mutable.Set[Array[Byte]] =
    mutable.Set[Array[Byte]]()

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
        val firstValidIndex = (context match {
          case Left(value) =>
            math.max(lastFoldUnfoldForMethod.getOrElse(value, 0), pair._2)
          case Right(_) => pair._2
        }) + 1
        val offset = rng.nextInt(listOfComponents.length - firstValidIndex + 1)
        (pair._1, firstValidIndex + offset)
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

  def byteToIntArray(arr: Array[Byte]): Array[Int] = {
    val intBuf = ByteBuffer
      .wrap(arr)
      .order(ByteOrder.BIG_ENDIAN)
      .asIntBuffer()
    val contents = new Array[Int](intBuf.remaining())
    intBuf.get(contents)
    contents
  }

  def permutationIDToPermutation(labelOut: LabelOutput, id: Array[Byte],
  ): LabelPermutation = {
    val contents = byteToIntArray(id)
    val perm = new LabelPermutation(labelOut)
    contents
      .foreach(index => {
        perm.addLabel(labelOut.labels(index))
      })
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
  ): Array[Byte] = {
    labels
      .map(template.indexOf(_))
      .flatMap(l => {
        val masked: Int = 0x0000 | l
        (0 to 3).map(i => ((masked >> ((3 - i) * 8)) & 0xff).toByte)
      })
      .toArray
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
  val completedSpecs: mutable.Set[Int] = mutable.Set[Int]()

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
        completedSpecs += label.specIndex
      case _ =>
    }
  }

  def labels: List[ASTLabel] = contents.toList

  def indices: Set[Int] = orderedIndices.toSet

  def imprecisionStatusList: List[Int] = {
    labelOutput.specsToSpecIndices.values.toList.sorted
      .map(index => {
        if (completedSpecs.contains(index)) 1 else 0
      })
  }

  def specStatusList: List[Int] = {
    labelOutput.labels
      .map(label => {
        if (this.labels.contains(label)) 1 else 0
      })
  }

  def exprIsComplete(template: Expression): Boolean =
    completedSpecs.nonEmpty &&
      labelOutput.specsToSpecIndices
        .contains(template) && completedSpecs.contains(
      labelOutput.specsToSpecIndices(template)
    )

  def id: String = {
    this.orderedIndices
      .map(i => {
        "%04X".format(i)
      })
      .mkString("")
  }

  def idArray: Array[Byte] = {
    val test = this.labels
      .flatMap(l => {
        val masked: Int = 0x0000 | labelOutput.pairToLabelOrdering(
          (l.specIndex, l.exprIndex))
        (0 to 3).map(i => ((masked >> ((3 - i) * 8)) & 0xff).toByte)
      })
    val compare = LabelTools.byteToIntArray(test.toArray)

    if (compare.length != this.orderedIndices.length) {
      throw new BenchmarkException("unequal!")
    }
    if (compare.length > 0) {
      for (i <- compare.indices) {
        this.orderedIndices(i) == compare(i)
      }
    }
    test.toArray
  }
}

class LabelException(str: String) extends Exception(str)
