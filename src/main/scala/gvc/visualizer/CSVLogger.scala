package gvc.visualizer
import gvc.visualizer.Bench.BenchmarkOutputFiles
import gvc.visualizer.Labeller.ASTLabel

import java.io.FileWriter
import java.nio.file.{Files, Path}
import scala.collection.mutable
case class PermutationID(pathID: Int, levelIndex: Int)


sealed trait ErrorType { val name: String }
object ErrorTypes {
  case object CC0 extends ErrorType { val name = "cc0" }
  case object Silicon extends ErrorType { val name = "silicon" }
  case object Execution extends ErrorType { val name = "execution" }
}
class CSVLogger(
                 programInFull: List[ASTLabel],
                 dest: BenchmarkOutputFiles,
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
                  errorType: ErrorType
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
                  hash: String
                ): Unit = {
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
