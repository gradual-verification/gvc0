package gvc.visualizer

import gvc.visualizer.Labeller.ASTLabel

import java.nio.file.Path
import scala.collection.mutable

case class LatticeElement(
    id: PermutationID,
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
      id: PermutationID,
      specsPresent: List[ASTLabel],
      originallyWrittenTo: Path
  ): LatticeElement = {
    val toAppend = LatticeElement(
      id metrics,
      specsPresent,
      originallyWrittenTo
    )
    elementMap += Labeller.hashPermutation(specsPresent)
    toAppend
  }
}
