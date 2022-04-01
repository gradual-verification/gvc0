package gvc.permutation

import gvc.CC0Wrapper.Performance
import gvc.permutation.Bench.BenchmarkOutputFiles

import java.io.FileWriter
import java.math.BigInteger
import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Columns {
  val performanceColumnNames: List[String] =
    List("id", "stress", "mean", "stdev", "min", "max")
  val mappingColumnNames: List[String] =
    List("id", "path_id", "level_id")
}

class ErrorCSVPrinter(file: Path) {
  if (Files.exists(file)) Files.delete(file)

  val writer = new FileWriter(file.toString, true)
  def formatSection(name: String, exitCode: Int): String =
    s"-----[ Error in $name, Exit: $exitCode ]-----\n"
  def log(name: String, exitCode: Int, err: String): Unit = {
    writer.write(formatSection(name, exitCode) + err + "\n\n\n")
    writer.flush()
  }
  def close(): Unit = writer.close()
}

class PerformanceCSVPrinter(out: Path) {
  if (Files.exists(out)) Files.delete(out)
  var writer = new FileWriter(out.toString, true)
  writer.write(
    Columns.performanceColumnNames.mkString(",") + '\n'
  )
  writer.flush()

  def close(): Unit = writer.close()

  def logID(
      id: String,
      stress: Int,
      perf: Performance
  ): Unit = {
    writer.write(
      List(id, stress.toString).mkString(",") + perf
        .toString() + '\n'
    )
    writer.flush()
  }
}

class CSVPrinter(files: BenchmarkOutputFiles, template: List[ASTLabel]) {
  if (Files.exists(files.metadata)) Files.delete(files.metadata)
  val metaWriter = new FileWriter(files.metadata.toString, true)
  if (Files.exists(files.levels)) Files.delete(files.levels)
  val mappingWriter = new FileWriter(files.levels.toString, true)

  val metadataColumnNames: String =
    (List("id") ++ template.map(_.hash)).mkString(",") + '\n'
  metaWriter.write(metadataColumnNames)
  metaWriter.flush()

  mappingWriter.write(
    Columns.mappingColumnNames.mkString(",") + '\n'
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
      permutation: Set[ASTLabel]
  ): String = {
    val entry = ListBuffer[String](id)
    template.foreach(label => {
      val toAppend = (if (permutation.contains(label)) 1 else 0).toString
      entry += toAppend
    })
    metaWriter.write(entry.mkString(",") + '\n')
    metaWriter.flush()
    id
  }

  def logStep(id: String, pathIndex: Int, levelIndex: Int): Unit = {
    mappingWriter.write(
      List(id, pathIndex, levelIndex).mkString(",") + '\n'
    )
    mappingWriter.flush()
  }
}
