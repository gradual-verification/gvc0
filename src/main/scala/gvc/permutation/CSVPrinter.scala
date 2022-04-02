package gvc.permutation

import gvc.CC0Wrapper.Performance
import gvc.permutation.Bench.{BenchmarkException, BenchmarkOutputFiles}

import java.io.FileWriter
import java.math.BigInteger
import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Extensions {
  def c0(basename: String): String = basename + ".c0"

  def out(basename: String): String = basename + ".out"

  def csv(basename: String): String = basename + ".csv"

  def log(basename: String): String = basename + ".log"

  def txt(basename: String): String = basename + ".txt"
}

object Columns {
  val performanceColumnNames: List[String] =
    List("id", "stress", "median", "mean", "stdev", "min", "max")
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
  var table =
    if (Files.exists(out)) generateTable(Files.readString(out))
    else mutable.Map[String, Set[Int]]()
  var writer = new FileWriter(out.toString, true)

  writer.write(
    Columns.performanceColumnNames.mkString(",") + '\n'
  )
  writer.flush()

  private def generateTable(contents: String): mutable.Map[String, Set[Int]] = {
    val lines: List[String] = contents.split('\n').toList
    val entries = lines.map(_.split('.').toList.map(_.trim))
    if (
      entries.isEmpty || !entries.head.equals(Columns.performanceColumnNames)
    ) {
      throw new BenchmarkException(
        s"The existing performance output at ${out.toString} is incorrectly formatted."
      )
    } else {
      val mapping = mutable.Map[String, Set[Int]]()
      entries
        .slice(1, entries.length)
        .foreach(entry => {
          if (mapping.contains(entry.head)) {
            mapping(entry.head) += entry(1)
          }
          mapping += (entry.head -> mutable.Set[Int](entry(1).toInt))
        })
      mapping
    }
  }

  def close(): Unit = writer.close()

  def exists(
      id: String,
      stress: Int
  ): Boolean =
    table.contains(id) && table(id).contains(stress)

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
