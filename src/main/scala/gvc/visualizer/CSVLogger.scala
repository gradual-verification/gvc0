package gvc.visualizer
import java.io.FileWriter
import java.nio.file.{Files, Path}
import scala.collection.mutable
case class PermutationID(pathID: Int, levelIndex: Int)

class CSVLogger(
    programInFull: List[ASTLabel],
    dest: BenchmarkOutputFiles
) {

  def append(path: Path, text: String): Unit = {
    val fw = new FileWriter(path.toFile, true);
    fw.write(text);
    fw.close()
  }

  append(
    dest.metrics,
    (Headers.metricsHeaders.foldLeft("")(_ + _ + ",") + '\n')
  )
  append(
    dest.lattice,
    (Headers.latticeHeaders.foldLeft("")(_ + _ + ",") + '\n')
  )

  if (!Files.exists(dest.errorDirectory)) {
    Files.createDirectory(dest.errorDirectory)
  }

  val errorMapping = mutable.Map[Int, String]()
  val metricsMapping = mutable.Map[String, Int]()

  def logFailure(
      permID: PermutationID,
      errorText: String,
      contents: List[ASTLabel]
  ): Unit = {
    val hash = errorText.hashCode()
    if (!errorMapping.contains(hash)) {
      Files.writeString(
        dest.errorDirectory.resolve(hash.toString + ".log"),
        errorText
      )
    }
    val entry =
      List(permID.pathID, permID.levelIndex, 0, hash).foldLeft("")(
        _ + _.toString + ","
      )
    append(dest.lattice, entry + "\n")
  }

  def logSuccess(
      permID: PermutationID,
      performanceMetrics: PerformanceMetrics,
      contents: List[ASTLabel]
  ): Unit = {
    val hash = Labeller.hashPermutation(contents)
    val entry = metricsMapping.get(hash)
    if (entry.isDefined) {
      val id = entry.get
      val latticeEntry =
        List(permID.pathID, permID.levelIndex, id, 0).foldLeft("")(
          _ + _.toString + ","
        )
      append(dest.lattice, latticeEntry)
    } else {
      val id = metricsMapping.size
      val metricsEntry = List(
        id,
        performanceMetrics.verification,
        performanceMetrics.execution,
        performanceMetrics.profiling.nConjuncts,
        performanceMetrics.profiling.nConjunctsEliminated
      ).foldLeft("")(_ + _.toString + ",")
      append(dest.metrics, metricsEntry)
      val latticeEntry =
        List(permID.pathID, permID.levelIndex, metricsMapping.size, 0).foldLeft(
          ""
        )(
          _ + _.toString + ","
        )
      append(dest.lattice, latticeEntry)
    }
  }

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
  }
}

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
      id,
      metrics,
      specsPresent,
      originallyWrittenTo
    )
    elementMap += Labeller.hashPermutation(specsPresent)
    toAppend
  }
}
