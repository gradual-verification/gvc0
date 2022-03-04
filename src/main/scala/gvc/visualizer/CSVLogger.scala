package gvc.visualizer

import gvc.visualizer.Labeller.ASTLabel

import java.io.FileWriter
import scala.collection.mutable
import scala.reflect.io.Directory
class CSVDestinationFiles(
    metrics: FileWriter,
    lattice: FileWriter,
    errorDirectory: Directory
)
case class PermutationID(pathID: Int, levelIndex: Int)

class CSVLogger(
    programInFull: List[ASTLabel],
    dest: CSVDestinationFiles
) {

  val errorMapping = mutable.Map[Int, String]()

  def logFailure(permID: PermutationID, errorText: String): Unit = {
    val hash = errorText.hashCode()
    if (errorMapping.contains(hash)) {
      val entry =
        List(permID.pathID, permID.levelIndex, 0, hash).foldleft("")(_ + _)
    } else {}
  }

  def logSuccess(
      permID: PermutationID,
      performanceMetrics: PerformanceMetrics,
      contents: List[ASTLabel]
  ): Unit = {}

  sealed trait ErrorType { val name: String }
  object ErrorTypes {
    case object CC0 { val name = "cc0" }
    case object Silicon { val name = "silicon" }
    case object Runtime { val name = "runtime" }
  }

  object Headers {
    val sharedHeaders = List("id")
    val metricsHeaders =
      sharedHeaders ++
        List(
          "verifier_time_ns",
          "execution_time_ns",
          "num_conjuncts",
          "num_conjuncts_elim"
        )

    val latticeHeaders =
      sharedHeaders ++
        List(
          "path_index",
          "level_index",
          "metrics_id",
          "error_id"
        )
    val errorHeaders = {
      sharedHeaders ++
        List(
          "type",
          "message"
        )
    }
  }
}
