package gvc.permutation

import gvc.CC0Wrapper.Performance
import gvc.Main.ProfilingInfo
import gvc.permutation.BenchConfig.BenchmarkOutputFiles
import java.io.FileWriter
import java.nio.file.{Files, Path}
import java.util.Date
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Extensions {
  def c0(basename: Object): String = basename.toString + ".c0"

  def out(basename: String): String = basename + ".out"

  def csv(basename: String): String = basename + ".csv"

  def log(basename: String): String = basename + ".log"

  def txt(basename: String): String = basename + ".txt"

  def remove(fullname: String): String = fullname.replaceFirst("[.][^.]+$", "")
}

object Columns {
  val performanceColumnNames: List[String] =
    List("stress", "iter", "median", "mean", "stdev", "min", "max")
  val mappingColumnNames: List[String] =
    List("id", "path_id", "level_id", "component_added")
  val pathColumnNames: List[String] =
    List("id", "path_hash")
  val conjunctColumnNames: List[String] =
    List("id", "conjuncts_total", "conjuncts_elim")
  def metadataColumnNames(template: List[ASTLabel]): List[String] =
    List("id") ++ template.map(_.hash)
}

class ErrorCSVPrinter(file: Path) {
  val writer = new FileWriter(file.toString, true)
  def formatSection(name: String, exitCode: Int): String =
    s"-----[ Error in $name, Exit: $exitCode, Time ${new Date().toString} ]-----\n"
  def log(name: String, exitCode: Int, err: String): Unit = {
    writer.write(formatSection(name, exitCode) + err + "\n\n\n")
    writer.flush()
  }
  def close(): Unit = writer.close()
}

class PerformanceCSVPrinter(out: Path, iterations: Int) {
  var table: mutable.Map[String, mutable.Set[Int]] =
    generatePerformanceTable(
      out
    )
  var writer = new FileWriter(out.toString, true)
  writer.write(
    (List("id") ++ Columns.performanceColumnNames).mkString(",") + '\n'
  )
  writer.flush()

  def close(): Unit = writer.close()

  def findMissingWorkloads(
      id: String,
      requested: List[Int]
  ): List[Int] = {
    if (table.contains(id)) {
      requested.toSet.diff(table(id)).toList
    } else {
      requested
    }
  }

  private def generatePerformanceTable(
      path: Path
  ): mutable.Map[String, mutable.Set[Int]] = {
    val mapping = mutable.Map[String, mutable.Set[Int]]()
    val entries: List[List[String]] =
      CSVIO.readEntries(path, List("id") ++ Columns.performanceColumnNames)

    def update(id: String, stress: Int): Unit = {
      if (mapping.contains(id)) {
        mapping(id) += stress
      } else {
        mapping += id -> mutable.Set(stress)
      }
    }
    entries
      .map(entry => (LabelTools.parseID(entry.head), entry(1)))
      .filter(pair => pair._1.isDefined && pair._2.matches("[0-9]+"))
      .foreach(pair => update(pair._1.get.toString(16), pair._2.toInt))
    mapping
  }

  def exists(
      id: String,
      stress: Int
  ): Boolean = {
    table.contains(id) && table(id).contains(stress)
  }

  def logID(
      id: String,
      stress: Int,
      perf: Performance
  ): Unit = {
    writer.write(
      List(id, stress.toString, iterations.toString).mkString(",") + "," + perf
        .toString() + '\n'
    )
    writer.flush()
  }
}

object CSVIO {

  def readEntries(input: Path): List[List[String]] = {
    if (Files.exists(input)) {
      val contents = Files.readString(input).trim
      val lines: List[String] = contents.split('\n').toList
      lines.map(_.split(',').toList.map(_.trim))
    } else {
      List()
    }
  }
  def readEntries(
      input: Path,
      columnNames: List[String]
  ): List[List[String]] = {

    var entries = readEntries(input)
    if (entries.isEmpty)
      Output.info(
        s"No preexisting output at ${input.toString}."
      )
    else if (!entries.head.equals(columnNames)) {
      Output.info(
        s"The preexisting output at ${input.toString} is missing or incorrectly formatted."
      )
      entries = List()
    } else {
      entries = entries
        .slice(1, entries.length)
        .filter(_.length == columnNames.length)
    }
    entries
  }
  def writeEntries(
      output: Path,
      entries: List[List[String]],
      columns: List[String]
  ): Unit = {
    val header = columns.mkString(",")
    val lines = entries.map(_.mkString(",")).mkString("\n")
    val contents = header + '\n' + lines
    Files.deleteIfExists(output)
    Files.writeString(output, contents)
  }

  def generateMetadataColumnEntry(
      id: String,
      template: Set[ASTLabel],
      permutation: Set[ASTLabel]
  ): List[String] = {
    val entry = ListBuffer[String](id)
    template.foreach(label => {
      val toAppend = (if (permutation.contains(label)) 1 else 0).toString
      entry += toAppend
    })
    entry.toList
  }
}

class MetadataCSVPrinter(
    files: BenchmarkOutputFiles,
    template: List[ASTLabel]
) {
  val metaWriter = new FileWriter(files.metadata.toString, true)
  val mappingWriter = new FileWriter(files.levels.toString, true)
  val permWriter = new FileWriter(files.permMap.toString, true)
  val conjunctWriter = new FileWriter(files.conjunctMap.toString, true)
  val metadataColumnNames: String =
    Columns.metadataColumnNames(template).mkString(",") + '\n'

  def close(): Unit = {
    metaWriter.close()
    mappingWriter.close()
    permWriter.close()
    conjunctWriter.close()
  }

  def logPath(
      index: Int,
      template: List[ASTLabel],
      permutation: List[ASTLabel]
  ): Unit = {
    val permID = LabelTools.hashPath(template, permutation)
    permWriter.write(index.toString + "," + permID.toString(16) + '\n')
    permWriter.flush()
  }

  def logPermutation(
      id: String,
      permutation: Set[ASTLabel]
  ): Unit = {
    val entry =
      CSVIO.generateMetadataColumnEntry(
        id,
        template.toSet,
        permutation
      )
    metaWriter.write(entry.mkString(",") + '\n')
    metaWriter.flush()
  }

  def logStep(
      id: String,
      pathIndex: Int,
      levelIndex: Int,
      componentAdded: Option[ASTLabel]
  ): Unit = {
    val labelText = componentAdded match {
      case Some(value) => value.hash
      case None        => "NA"
    }
    mappingWriter.write(
      List(id, pathIndex, levelIndex, labelText).mkString(",") + '\n'
    )
    mappingWriter.flush()
  }

  def logConjuncts(id: String, perf: ProfilingInfo): Unit = {
    val conjunctEntry =
      List(id, perf.nConjuncts.toString, perf.nConjunctsEliminated.toString)
        .mkString(",") + '\n'
    conjunctWriter.write(conjunctEntry)
    conjunctWriter.flush()
  }
}
