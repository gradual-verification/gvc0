package gvc.permutation

import gvc.CC0Wrapper.Performance
import gvc.permutation.Bench.{BenchmarkOutputFiles, csv}

import java.io.FileWriter
import java.math.BigInteger
import java.nio.file.Path
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Columns {
  val performanceColumnNames: List[String] =
    List("stress", "mean", "stdev", "min", "max")
  val mappingColumnNames: List[String] =
    List("id", "path_id", "level_id")
}

class ErrorCSVPrinter(file: Path) {
  val writer = new FileWriter(file.toString)
  def formatSection(name: String, exitCode: Int): String =
    s"-----[ Error in $name, Exit: $exitCode ]-----\n"
  def log(name: String, exitCode: Int, err: String): Unit = {
    writer.write(formatSection(name, exitCode) + err + "\n")
    writer.flush()
  }
  def close(): Unit = writer.close()
}

class PerformanceCSVPrinter(out: Path) {
  var currentWriter: Option[(Option[String], FileWriter)] = None

  private def replaceWriter(id: String): FileWriter = {
    val contents =
      (Some(id), new FileWriter(out.resolve(csv(id)).toString))
    if (currentWriter.isDefined) currentWriter.get._2.close()
    currentWriter = Some(contents)
    contents._2.write(
      Columns.performanceColumnNames.foldRight("")(
        _ + "," + _
      ) + '\n'
    )
    contents._2.flush()
    contents._2
  }

  def logID(
      id: String,
      stress: Int,
      perf: Performance
  ): Unit = {
    val writer: FileWriter = currentWriter match {
      case Some(value) =>
        if (value._1.equals(id)) {
          value._2
        } else {
          value._2.close()
          replaceWriter(id)
        }
      case None => replaceWriter(id)

    }
    writer.write(perf.toString(stress) + '\n')
    writer.flush()
  }
}

class CSVPrinter(files: BenchmarkOutputFiles, template: List[ASTLabel]) {
  val metaWriter = new FileWriter(files.metadata.toString)
  val mappingWriter = new FileWriter(files.levels.toString)

  val metadataColumnNames: String =
    (List("id") ++ template.map(_.hash)).foldRight("")(_ + "," + _) + '\n'
  metaWriter.write(metadataColumnNames)
  metaWriter.flush()

  mappingWriter.write(
    Columns.mappingColumnNames.foldRight("")(_ + "," + _) + '\n'
  )
  mappingWriter.flush()

  def close(): Unit = {
    metaWriter.close()
    mappingWriter.close()
  }

  def createID(permutation: mutable.TreeSet[ASTLabel]): String = {
    new BigInteger(
      template
        .map(label => {
          (if (permutation.contains(label)) 1 else 0).toString
        })
        .foldRight("")(_ + _),
      2
    ).toString(16)
  }

  def logPermutation(
      id: String,
      permutation: mutable.TreeSet[ASTLabel]
  ): String = {
    val entry = ListBuffer[String](id)
    template.foreach(label => {
      val toAppend = (if (permutation.contains(label)) 1 else 0).toString
      entry += toAppend
    })
    metaWriter.write(entry.foldRight("")(_ + "," + _) + '\n')
    metaWriter.flush()
    id
  }

  def logStep(id: String, pathIndex: Int, levelIndex: Int): Unit = {
    mappingWriter.write(
      List(id, pathIndex, levelIndex).foldRight("")(_ + "," + _) + '\n'
    )
    mappingWriter.flush()
  }
}
