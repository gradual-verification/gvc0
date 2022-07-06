package gvc.benchmarking

import gvc.CC0Wrapper.Performance
import gvc.Main.ProfilingInfo
import gvc.benchmarking.BenchConfig.{BenchmarkConfig, BenchmarkOutputFiles}
import gvc.benchmarking.Timing.TimedVerification

import java.io.FileWriter
import java.math.BigInteger
import java.nio.file.{Files, Path}
import java.util.Date

object Extensions {
  def c0(basename: Object): String = basename.toString + ".c0"

  def out(basename: String): String = basename + ".out"

  def csv(basename: String): String = basename + ".csv"

  def log(basename: String): String = basename + ".log"

  def txt(basename: String): String = basename + ".txt"

  def remove(fullname: String): String = fullname.replaceFirst("[.][^.]+$", "")
}

object Columns {
  val timingStatColumnNames: List[String] =
    List("iter", "95th", "5th", "median", "mean", "stdev", "min", "max")
  val performanceColumnNames: List[String] =
    List("stress") ++ timingStatColumnNames
  val mappingColumnNames: List[String] =
    List("id", "path_id", "level_id", "component_added")
  val pathColumnNames: List[String] =
    List("id", "path_hash")
  val conjunctColumnNames: List[String] =
    List("id", "conjuncts_total", "conjuncts_elim")
  val staticTimingColumnNames: List[String] =
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

class StaticCSVPrinter(benchConfig: BenchmarkConfig) extends {

  private val translationWriter =
    new FileWriter(benchConfig.files.translationPerformance.toString, true)
  private val verificationWriter =
    new FileWriter(benchConfig.files.verificationPerformance.toString, true)
  private val instrumentationWriter =
    new FileWriter(benchConfig.files.instrumentationPerformance.toString, true)
  val writers: List[FileWriter] =
    List(translationWriter, verificationWriter, instrumentationWriter)

  writers.foreach(l => {
    l.write((List("id") ++ Columns.timingStatColumnNames).mkString(",") + '\n')
    l.flush()
  })
  def close(): Unit = {
    writers.foreach(_.close())
  }

  def log(
      id: String,
      perf: TimedVerification
  ): Unit = {
    (writers zip List(
      perf.translation,
      perf.verification,
      perf.instrumentation
    )).foreach(t => {
      t._1.write(
        List(id, benchConfig.workload.iterations.toString)
          .mkString(",") + "," + t._2.toString() + '\n'
      )
      t._1.flush()
    })
  }
}

class DynamicCSVPrinter(
    benchConfig: BenchmarkConfig,
    execType: ExecutionType
) {

  var compilationWriter = new FileWriter(
    (execType match {
      case ExecutionType.Gradual =>
        benchConfig.files.compilationPerformanceGradual
      case ExecutionType.FullDynamic =>
        benchConfig.files.compilationPerformanceDynamic
      case ExecutionType.FramingOnly =>
        benchConfig.files.compilationPerformanceFraming
      case _ => "./compilation_perf.csv"
    }).toString,
    true
  )
  var executionWriter = new FileWriter(
    (execType match {
      case ExecutionType.Gradual =>
        benchConfig.files.executionPerformanceGradual
      case ExecutionType.FullDynamic =>
        benchConfig.files.executionPerformanceDynamic
      case ExecutionType.FramingOnly =>
        benchConfig.files.executionPerformanceFraming
      case _ => "./dyn_perf.csv"
    }).toString,
    true
  )

  val writers: List[FileWriter] = List(compilationWriter, executionWriter)
  compilationWriter.write(
    (List("id") ++ Columns.timingStatColumnNames).mkString(",") + '\n'
  )
  executionWriter.write(
    (List("id") ++ Columns.performanceColumnNames).mkString(",") + '\n'
  )

  def close(): Unit = {
    writers.foreach(_.close())
  }
  def logCompilation(
      id: String,
      perf: Performance
  ): Unit = {
    compilationWriter.write(
      id + "," + perf.toString() + '\n'
    )
    compilationWriter.flush()
  }

  def logExecution(
      id: String,
      stress: Int,
      perf: Performance
  ): Unit = {
    executionWriter.write(
      List(id, stress.toString, benchConfig.workload.iterations.toString)
        .mkString(",") + "," + perf
        .toString() + '\n'
    )
    executionWriter.flush()
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
      permutation: LabelPermutation
  ): List[String] = {
    List(id) ++ permutation.specStatusList.map(
      _.toString
    ) ++ permutation.imprecisionStatusList
      .map(_.toString)
  }
}

class MetadataCSVPrinter(
    files: BenchmarkOutputFiles,
    template: List[ASTLabel]
) {
  val metaWriter = new FileWriter(files.metadata.toString, true)
  val metadataColumnNames: String =
    Columns.metadataColumnNames(template).mkString(",") + '\n'
  metaWriter.write(metadataColumnNames)
  metaWriter.flush()

  val mappingWriter = new FileWriter(files.levels.toString, true)
  mappingWriter.write(Columns.mappingColumnNames.mkString(",") + '\n')
  mappingWriter.flush()

  val pathWriter = new FileWriter(files.permMap.toString, true)
  pathWriter.write(Columns.pathColumnNames.mkString(",") + '\n')
  pathWriter.flush()

  val conjunctWriter = new FileWriter(files.conjunctMap.toString, true)
  conjunctWriter.write(Columns.conjunctColumnNames.mkString(",") + '\n')
  conjunctWriter.flush()

  def close(): Unit = {
    metaWriter.close()
    mappingWriter.close()
    pathWriter.close()
    conjunctWriter.close()
  }

  def logPath(
      index: Int,
      template: List[ASTLabel],
      permutation: List[ASTLabel]
  ): Unit = {
    val permID = LabelTools.hashPath(template, permutation)
    pathWriter.write(index.toString + "," + permID.toString(16) + '\n')
    pathWriter.flush()
  }
  def logPermutation(
      id: String,
      permutation: LabelPermutation
  ): Unit = {
    val entry =
      CSVIO.generateMetadataColumnEntry(
        id,
        permutation
      )
    metaWriter.write(entry.mkString(",") + '\n')
    metaWriter.flush()
  }

  def logStep(
      id: BigInteger,
      pathIndex: Int,
      levelIndex: Int,
      componentAdded: Option[ASTLabel]
  ): Unit = {
    val labelText = componentAdded match {
      case Some(value) => value.hash
      case None        => "NA"
    }
    mappingWriter.write(
      List(id.toString(16), pathIndex, levelIndex, labelText)
        .mkString(",") + '\n'
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
