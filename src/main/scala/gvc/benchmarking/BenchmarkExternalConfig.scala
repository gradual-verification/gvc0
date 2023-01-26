package gvc.benchmarking

import gvc.Config
import gvc.Config.error
import gvc.benchmarking.DAO.DynamicMeasurementMode
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode

import java.nio.file.{Files, InvalidPathException, Path, Paths}
import scala.xml.{Elem, NodeSeq, XML}
import scala.language.implicitConversions
import scala.language.postfixOps
import scala.reflect.io.Directory

case class BenchmarkDBCredentials(
    url: String,
    username: String,
    password: String
)

case class BenchmarkWorkload(
    iterations: Int,
    staticIterations: Int,
    nPaths: Int,
    stress: Option[StressConfiguration],
    programCases: List[WorkloadProgramEntry]
)

case class WorkloadProgramEntry(matches: List[String],
                                iterations: Option[Int],
                                workload: StressConfiguration,
                                isDefault: Boolean)

case class IterConfiguration(static: Int, dynamic: Int)

trait StressConfiguration

case class StressBounded(wLower: Int, wUpper: Int, wStep: Int)
    extends StressConfiguration

case class StressList(wList: List[Int]) extends StressConfiguration

case class StressSingular(stressValue: Int) extends StressConfiguration

trait BenchmarkingConfig

case class PipelineModifiers(exclusiveMode: Option[DynamicMeasurementMode],
                             saveErroredPerms: Option[Path],
                             onlyVerify: Boolean,
                             onlyCompile: Boolean,
                             onlyBenchmark: Boolean,
                             onlyErrors: Boolean,
                             nicknameSensitivity: Boolean,
                             skipVerification: Boolean)

case class RecreatorConfig(version: String,
                           db: BenchmarkDBCredentials,
                           sources: List[Path],
                           permToRecreate: Long,
                           modifiers: PipelineModifiers)
    extends BenchmarkingConfig

case class PopulatorConfig(version: String,
                           pathQuantity: Option[Int],
                           db: BenchmarkDBCredentials,
                           sources: List[Path])
    extends BenchmarkingConfig

case class MonitorConfig(db: BenchmarkDBCredentials) extends BenchmarkingConfig

case class ExecutorConfig(version: String,
                          hardware: String,
                          nickname: String,
                          workload: BenchmarkWorkload,
                          db: BenchmarkDBCredentials,
                          modifiers: PipelineModifiers,
                          sources: List[Path],
                          timeoutMinutes: Int,
                          profilingDirectory: Option[Path])
    extends BenchmarkingConfig

case class ExportConfig(version: String,
                        hardware: String,
                        workload: BenchmarkWorkload,
                        quantity: Option[Int],
                        modifiers: PipelineModifiers,
                        benchmarkDBCredentials: BenchmarkDBCredentials,
                        outputDir: Option[String])

case class BenchmarkConfigResults(
    version: String,
    hardware: Option[String],
    nickname: Option[String],
    credentials: BenchmarkDBCredentials,
    sources: List[Path],
    workload: Option[BenchmarkWorkload],
    pathQuantity: Option[Int],
    modifiers: PipelineModifiers,
    profilingDirectory: Option[Path],
    outputDir: Option[String],
    iter: IterConfiguration,
    timeout: Int
)

object BenchmarkExternalConfig {

  class ChildSelectable(ns: NodeSeq) {
    def \* : NodeSeq = ns flatMap {
      _ match {
        case e: Elem => e.child
        case _       => NodeSeq.Empty
      }
    }
  }

  implicit def nodeSeqIsChildSelectable(xml: NodeSeq): ChildSelectable =
    new ChildSelectable(xml)

  private object Defaults {
    val timeout: Int = 2 * 60
  }

  def parseMonitor(rootConfig: Config): MonitorConfig = {
    val resolved = parseConfig(rootConfig)
    MonitorConfig(
      resolved.credentials
    )
  }

  def parseRecreator(rootConfig: Config): RecreatorConfig = {
    val resolved = parseConfig(rootConfig)
    rootConfig.recreatePerm match {
      case Some(value) =>
        RecreatorConfig(resolved.version,
                        resolved.credentials,
                        resolved.sources,
                        value,
                        resolved.modifiers)
      case None => error("Expected an integer value passed to --recreate.")
    }
  }

  def parseExecutor(rootConfig: Config): ExecutorConfig = {

    val resolved = parseConfig(rootConfig)
    val profilingDirectory: Option[Path] = resolved.profilingDirectory match {
      case Some(value) => Some(value)
      case None =>
        rootConfig.profilingDirectory match {
          case Some(value) =>
            Some(overwriteDirectory(value))
          case None =>
            if (rootConfig.profilingEnabled) {
              Some(Paths.get("./"))
            } else {
              None
            }
        }
    }

    resolved.hardware match {
      case Some(hValue) =>
        resolved.workload match {
          case Some(wValue) =>
            resolved.nickname match {
              case Some(nValue) =>
                ExecutorConfig(
                  resolved.version,
                  hValue,
                  nValue,
                  wValue,
                  resolved.credentials,
                  resolved.modifiers,
                  resolved.sources,
                  resolved.timeout,
                  profilingDirectory
                )
              case None => error("A <nickname> must be provided.")
            }

          case None => error("A <workload> configuration must be provided.")
        }

      case None => error("A <hardware> ID must be provided.")
    }
  }

  def parsePopulator(rootConfig: Config): PopulatorConfig = {
    val resolved = parseConfig(rootConfig)

    PopulatorConfig(resolved.version,
                    resolved.pathQuantity,
                    resolved.credentials,
                    resolved.sources)

  }

  def parseExport(rootConfig: Config): ExportConfig = {
    val resolved = parseConfig(rootConfig)
    val optionalOutputDirectory = resolved.outputDir match {
      case Some(oValue) => Some(oValue)
      case None         => rootConfig.exportDirectory
    }
    resolved.hardware match {
      case Some(hValue) =>
        resolved.workload match {
          case Some(wValue) =>
            ExportConfig(resolved.version,
                         hValue,
                         wValue,
                         resolved.pathQuantity,
                         resolved.modifiers,
                         resolved.credentials,
                         optionalOutputDirectory)
          case None => error("A <workload> configuration must be provided.")
        }
      case None => error("A <hardware> ID must be provided.")
    }
  }

  private def parseConfig(rootConfig: Config): BenchmarkConfigResults = {
    val configPath = rootConfig.config.get
    val xml = XML.loadFile(configPath.toFile)
    val benchmarkRoot = xml \\ "benchmark"
    if (benchmarkRoot.isEmpty) {
      error("Expected <benchmark> element.")
    } else {
      val version =
        resolveFallback(benchmarkRoot, "version", rootConfig.versionString)
      val hardware =
        resolveFallbackOptional(benchmarkRoot,
                                "hardware",
                                rootConfig.hardwareString)
      val nickname =
        resolveFallbackOptional(benchmarkRoot,
                                "nickname",
                                rootConfig.nicknameString)
      val quantity =
        intOption(benchmarkRoot \ "quantity")

      val timeout = intOption(benchmarkRoot \ "timeout")

      val sourceDirElement = benchmarkRoot \ "source-dir"
      if (sourceDirElement.isEmpty || sourceDirElement.text.trim.isEmpty) {
        error("Expected <source-dir> field.")
      }
      val sourceDirText = sourceDirElement.text
      val sourceDirPath = validateDirectory(sourceDirText, "source-dir")

      val c0SourceFiles = sourceDirPath.toFile
        .listFiles()
        .filter(_.isFile)
        .toList
        .filter(p => {
          p.getName.endsWith(".c0")
        })
        .map(_.toPath)
      val fileCollection = rootConfig.sourceFile match {
        case Some(value) => c0SourceFiles ++ List(Paths.get(value))
        case None        => c0SourceFiles
      }

      val outputDir = benchmarkRoot \ "output-dir"
      val outputDirText =
        if (outputDir.isEmpty || outputDir.text.trim.isEmpty) None
        else Some(outputDir.text.trim)

      val credentials = parseDB(benchmarkRoot \ "db", rootConfig)

      val workload = parseWorkload(benchmarkRoot \ "workload")

      val iter = parseIter(benchmarkRoot \ "iter")

      val modifiers = parsePipelineModifiers(rootConfig, benchmarkRoot)

      val profilingDirElement = benchmarkRoot \ "profiling-dir"
      val profilingDirText = profilingDirElement.text

      val profilingDir =
        if (profilingDirElement.isEmpty || profilingDirElement.text.trim.isEmpty) {
          None
        } else {
          Some(overwriteDirectory(profilingDirText))
        }

      BenchmarkConfigResults(version,
                             hardware,
                             nickname,
                             credentials,
                             fileCollection,
                             workload,
                             quantity,
                             modifiers,
                             profilingDir,
                             outputDirText,
                             iter,
                             timeout.getOrElse(Defaults.timeout),
      )
    }
  }

  def generateStressList(stress: StressConfiguration): List[Int] = {
    val stepList = stress match {
      case singular: StressSingular => List(singular.stressValue)
      case list: StressList         => list.wList.distinct
      case stepwise: StressBounded =>
        (stepwise.wLower to stepwise.wUpper by stepwise.wStep).toList
    }
    stepList
  }

  private def resolveFallback(xml: NodeSeq,
                              field: String,
                              fallback: Option[String]): String = {
    fallback match {
      case Some(value) => value
      case None =>
        val provided = xml \ field
        if (provided.nonEmpty) {
          provided.text.trim

        } else {
          error(
            s"No $field string has been provided, either as a command line argument (--$field) or configuration file field.")
        }

    }
  }

  private def resolveStringList(xml: NodeSeq): List[String] = {
    xml.text.split(',').map(_.trim).toList
  }

  private def resolveFallbackOptional(
      xml: NodeSeq,
      field: String,
      fallback: Option[String]): Option[String] = {
    fallback match {
      case Some(_) => fallback
      case None =>
        val provided = xml \ field
        if (provided.nonEmpty) {
          Some(provided.text.trim)
        } else {
          None
        }
    }
  }

  private def singleton(xml: NodeSeq, label: String): Boolean = {
    (xml \*).exists(p => {
      p.label.equals(label)
    })
  }

  private def parsePipelineModifiers(config: Config,
                                     xml: NodeSeq): PipelineModifiers = {
    val onlyDynamic =
      if (singleton(xml, "only-dynamic")) Some(DynamicMeasurementMode.Dynamic)
      else None
    val onlyFraming =
      if (singleton(xml, "only-framing")) Some(DynamicMeasurementMode.Framing)
      else None
    val onlyGradual =
      if (singleton(xml, "only-gradual")) Some(DynamicMeasurementMode.Gradual)
      else None
    val saveErroredPerms =
      resolveFallbackOptional(xml, "save-errored-perms", None)
    val erroredPermsDirectory = saveErroredPerms match {
      case Some(value) =>
        val dirPath = Paths.get(value)
        if (Files.exists(Paths.get(value))) {
          error(
            s"Cannot save errored permutations to '$value'; the directory already exists.")
        } else {
          Files.createDirectory(dirPath)
        }
        Some(dirPath)
      case None => None
    }

    val excluded =
      List(onlyDynamic, onlyGradual, onlyFraming).filter(_.nonEmpty).map(_.get)
    if (excluded.length > 1) {
      error(
        "Multiple benchmarking modes were set as exclusive (e.g. <only-[mode])/>)")
    }

    val benchmark = singleton(xml, "export-only-benchmark") || config.onlyBenchmark
    val verify = singleton(xml, "export-only-verification") || config.onlyVerify
    val compile = singleton(xml, "only-compile") || config.onlyCompile
    val errors = singleton(xml, "export-only-errors") || config.onlyErrors
    val enabled = List(benchmark, verify, compile, errors).count(b => b)
    if (enabled > 1) {
      error(
        "Multiple export modes were set as exclusive (e.g. <only-[mode])/>)")
    }
    PipelineModifiers(
      exclusiveMode = excluded.headOption,
      saveErroredPerms = erroredPermsDirectory,
      nicknameSensitivity = singleton(xml, "nickname-sensitive"),
      onlyBenchmark = singleton(xml, "export-only-benchmark") || config.onlyBenchmark,
      onlyVerify = singleton(xml, "export-only-verification") || config.onlyVerify,
      onlyCompile = singleton(xml, "only-compile") || config.onlyCompile,
      onlyErrors = singleton(xml, "export-only-errors") || config.onlyErrors,
      skipVerification = singleton(xml, "skip-verification")
    )

  }

  private def parseDB(xml: NodeSeq,
                      rootConfig: Config): BenchmarkDBCredentials = {
    val url = resolveFallback(xml, "url", rootConfig.dbURLString)
    val username = resolveFallback(xml, "username", rootConfig.dbUserString)
    val password = resolveFallback(xml, "password", rootConfig.dbPassString)
    BenchmarkDBCredentials(
      url,
      username,
      password,
    )
  }

  private def intOrError(xml: NodeSeq, errorText: String): Int = {
    try {
      xml.text.toInt
    } catch {
      case _: NumberFormatException =>
        error(errorText)
    }
  }

  private def intOption(xml: NodeSeq): Option[Int] = {
    try {
      Some(xml.text.toInt)
    } catch {
      case _: NumberFormatException =>
        None
    }
  }

  private def validateDirectory(pathText: String,
                                tag: String): java.nio.file.Path = {
    try {
      val converted = Paths.get(pathText)
      if (Files.exists(converted)) {
        if (Files.isDirectory(converted)) {
          converted
        } else {
          error(
            s"<$tag>: Expected a directory but found a regular file: $pathText")
        }
      } else {
        Files.createDirectory(converted)
      }
    } catch {
      case _: InvalidPathException => {}
      error(s"<$tag>: Invalid path format: $pathText")
    }
  }

  private def overwriteDirectory(pathText: String): java.nio.file.Path = {
    val converted = Paths.get(pathText)
    if (Files.exists(converted)) {
      new Directory(converted.toFile).deleteRecursively()
    }
    Files.createDirectory(converted)
  }

  private def validateFile(pathText: String,
                           tag: String): java.nio.file.Path = {
    try {
      val converted = Paths.get(pathText)
      if (Files.exists(converted)) {
        if (Files.isRegularFile(converted)) {
          converted
        } else {
          error(s"<$tag>: Expected a file but found a directory: $pathText")
        }
      } else {
        error(s"<$tag>: The specified file $pathText doesn't exist.")
      }
    } catch {
      case _: InvalidPathException => {}
      error(s"<$tag>: Invalid path format: $pathText")
    }
  }

  private def parseWorkload(
      workloadRoot: NodeSeq): Option[BenchmarkWorkload] = {
    if (workloadRoot.isEmpty) {
      None
    } else {
      val paths = workloadRoot \ "paths"
      val iterations = workloadRoot \ "iterations"
      val staticIterations = workloadRoot \ "static-iterations"
      val byProgram: List[WorkloadProgramEntry] =
        (workloadRoot \ "by-program" \ "p").toList
          .map(parseWorkloadProgramEntry)

      val iterQuantity =
        if (iterations.isEmpty) 1
        else
          intOrError(
            iterations,
            s"Expected an integer for <iterations>, but found: '${iterations.text}")
      val staticIterQuantity =
        if (staticIterations.isEmpty) 1
        else
          intOrError(
            staticIterations,
            s"Expected an integer for <static-iterations>, but found: '${staticIterations.text}")
      val pathQuantity =
        if (paths.isEmpty) 1
        else
          intOrError(
            paths,
            s"Expected an integer for <paths>, but found: '${paths.text}'")
      val stress = parseStress(workloadRoot \ "stress")

      val numberDefault = byProgram.count(e => e.isDefault)
      if (numberDefault > 1) {
        error("Multiple <by-program> entries match everything ('*').")
      }
      Some(
        BenchmarkWorkload(iterQuantity,
                          staticIterQuantity,
                          pathQuantity,
                          stress,
                          byProgram))
    }
  }

  def parseWorkloadProgramEntry(xml: NodeSeq): WorkloadProgramEntry = {
    val names = resolveStringList(xml \ "match")
    val namesFiltered = names.map(n => n.replace("\\*", "*"))
    val isDefault = namesFiltered.contains("*")
    val namesWithoutWildcard = namesFiltered.filter(i => i != "*")

    val stress = parseStress(xml \ "stress")
    val iterations = intOption(xml \ "iterations")
    if (names.isEmpty) {
      error(
        "At least one program name must be provided in <match> for each <p> under <by-program>.")
    }
    if (stress.isEmpty) {
      error(
        s"No stress configuration was provided for <match>${names.mkString(",")}</match>")
    }
    WorkloadProgramEntry(namesWithoutWildcard,
                         iterations,
                         stress.get,
                         isDefault)
  }

  private def parseStress(xml: NodeSeq): Option[StressConfiguration] = {
    val listed = parseStressListed(xml \ "list")
    val singular = parseStressSingular(xml \ "singular")
    val bounded = parseStressBounded(xml \ "bounded")
    val specified = List(listed, singular, bounded).filter(_.nonEmpty)
    if (specified.length > 1) {
      error(
        "Only one workload specification method can be used for <stress>; multiple were found.")
    } else {
      if (specified.nonEmpty) {
        specified.head match {
          case Some(value) => Some(value)
          case None =>
            error("Missing workload specification under <stress>")
        }
      } else {
        None
      }
    }
  }

  private def parseStressBounded(xml: NodeSeq): Option[StressConfiguration] = {
    if (xml.isEmpty) {
      None
    } else {
      val lower = xml \ "lower"
      val lowerQuantity =
        if (lower.isEmpty) 0
        else
          intOrError(
            lower,
            s"Expected a single integer for <lower>; found: '${lower.text}'")

      val upper = xml \ "upper"
      val upperQuantity = intOrError(
        upper,
        s"Expected a single integer for <upper>; found: '${upper.text}'")
      val step = xml \ "step"
      val stepQuantity =
        intOrError(
          step,
          s"Expected a single integer for <step>; found: '${step.text}'")

      Some(StressBounded(lowerQuantity, upperQuantity, stepQuantity))
    }
  }

  private def parseStressSingular(xml: NodeSeq): Option[StressConfiguration] = {
    if (xml.isEmpty) {
      None
    } else {
      val singular = intOrError(
        xml,
        s"Expected a single integer for <singular>; found: '${xml.text}'")
      Some(StressSingular(singular))
    }
  }

  private def parseIter(xml: NodeSeq): IterConfiguration = {
    val static = intOption(xml \ "static")
    val dynamic = intOption(xml \ "dynamic")
    IterConfiguration(static.getOrElse(1), dynamic.getOrElse(10))
  }

  private def parseStressListed(xml: NodeSeq): Option[StressConfiguration] = {
    if (xml.isEmpty) {
      None
    } else {
      if (xml.text.matches("[0-9]+(,[0-9]+)*")) {
        Some(StressList(xml.text.split(',').map(s => s.trim.toInt).toList))
      } else {
        error(
          "Invalid input for <list>; expected a comma-separated list of integers"
        )
      }
    }
  }
}
