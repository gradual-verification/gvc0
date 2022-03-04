package gvc.visualizer

import gvc.visualizer.Labeller.ASTLabel

import java.nio.file.Path
import scala.collection.mutable

case class LatticeElement(
    metrics: PerformanceMetrics,
    specsPresent: List[ASTLabel],
    originallyWrittenTo: Path
)

class Lattice {
  val levels: mutable.ListBuffer[mutable.ListBuffer[LatticeElement]] =
    mutable.ListBuffer[mutable.ListBuffer[LatticeElement]]()
  val elementMap: mutable.Map[String, LatticeElement] =
    mutable.Map[String, LatticeElement]()

  def get(hash: String): Option[LatticeElement] = {
    elementMap.get(hash)
  }
  def add(
      metrics: PerformanceMetrics,
      specsPresent: List[ASTLabel],
      originallyWrittenTo: Path
  ): LatticeElement = {
    val toAppend = LatticeElement(
      metrics,
      specsPresent,
      originallyWrittenTo
    )
    elementMap += specsPresent.foldLeft("")(_ + _.hash) -> toAppend
    toAppend
  }
  def createCSVEntry(
      latticeElement: LatticeElement,
      sourceFileName: String
  ): String = {
    val entry = mutable.ListBuffer[String]()
    entry += sourceFileName
    entry += latticeElement.specsPresent.length.toString
    entry += latticeElement.metrics.execution.toString
    entry += latticeElement.metrics.verification.toString
    entry.foldRight("")(_ + "," + _) + "\n"
  }
}
