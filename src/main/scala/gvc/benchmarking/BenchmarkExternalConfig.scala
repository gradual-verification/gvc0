package gvc.benchmarking

import gvc.Config
import gvc.Config.error

import java.nio.file.{Files, InvalidPathException, Path, Paths}
import scala.xml.{NodeSeq, XML}

class BenchmarkConfigException(message: String) extends Exception(message)

case class BenchmarkDBCredentials(
    url: String,
    username: String,
    password: String
)

case class BenchmarkIO(
    outputDir: java.nio.file.Path,
    input: List[java.nio.file.Path]
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

case class PlatformIdentification(versionID: String, hardwareID: String)

trait BenchmarkingConfig

case class PipelineModifiers(onlyVerify: Boolean,
                             onlyCompile: Boolean,
                             disableBaseline: Boolean)

case class RecreatorConfig(version: String,
                           db: BenchmarkDBCredentials,
                           sources: List[Path],
                           permToRecreate: Long)
    extends BenchmarkingConfig

case class PopulatorConfig(version: String,
                           pathQuantity: Option[Int],
                           db: BenchmarkDBCredentials,
                           sources: List[Path],
                           workload: BenchmarkWorkload)
    extends BenchmarkingConfig

case class MonitorConfig(db: BenchmarkDBCredentials, outputDirectory: Path)
    extends BenchmarkingConfig

case class ExecutorConfig(version: String,
                          hardware: String,
                          nickname: Option[String],
                          iter: IterConfiguration,
                          db: BenchmarkDBCredentials,
                          sources: List[Path])
    extends BenchmarkingConfig

case class BenchmarkConfigResults(
    version: String,
    hardware: Option[String],
    nickname: Option[String],
    credentials: BenchmarkDBCredentials,
    sources: List[Path],
    workload: Option[BenchmarkWorkload],
    pathQuantity: Option[Int],
    modifiers: PipelineModifiers,
    outputDir: Option[String],
    iter: IterConfiguration
)

object BenchmarkExternalConfig {

  private object Names {
    val defaultOutputDirectory = "./data"
  }

  def parseMonitor(rootConfig: Config): MonitorConfig = {
    val resolved = parseConfig(rootConfig)
    MonitorConfig(
      resolved.credentials,
      Paths.get(resolved.outputDir.getOrElse(Names.defaultOutputDirectory))
    )
  }

  def parseRecreator(rootConfig: Config): RecreatorConfig = {
    val resolved = parseConfig(rootConfig)
    rootConfig.recreatePerm match {
      case Some(value) =>
        RecreatorConfig(resolved.version,
                        resolved.credentials,
                        resolved.sources,
                        value)
      case None => error("Expected an integer value passed to --recreate.")
    }
  }

  def parseExecutor(rootConfig: Config): ExecutorConfig = {
    val resolved = parseConfig(rootConfig)
    resolved.hardware match {
      case Some(hValue) =>
        ExecutorConfig(
          resolved.version,
          hValue,
          resolved.nickname,
          resolved.iter,
          resolved.credentials,
          resolved.sources
        )
      case None => error("A <hardware> must be provided.")
    }
  }

  def parsePopulator(rootConfig: Config): PopulatorConfig = {
    val resolved = parseConfig(rootConfig)
    resolved.workload match {
      case Some(wValue) =>
        PopulatorConfig(resolved.version,
                        resolved.pathQuantity,
                        resolved.credentials,
                        resolved.sources,
                        wValue)
      case None => error("A <workload> must be provided.")
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
        resolveFallback("version", benchmarkRoot, rootConfig.versionString)
      val hardware =
        resolveFallbackOptional("hardware",
                                benchmarkRoot,
                                rootConfig.hardwareString)
      val nickname =
        resolveFallbackOptional("nickname",
                                benchmarkRoot,
                                rootConfig.nicknameString)
      val quantity =
        intOption(benchmarkRoot \ "quantity")

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

      val modifiers = parsePipelineModifiers(benchmarkRoot)

      BenchmarkConfigResults(version,
                             hardware,
                             nickname,
                             credentials,
                             fileCollection,
                             workload,
                             quantity,
                             modifiers,
                             outputDirText,
                             iter)
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

  private def resolveFallback(field: String,
                              xml: NodeSeq,
                              fallback: Option[String]) = {
    fallback match {
      case Some(value) => value
      case None => {
        val provided = xml \ field
        if (provided.nonEmpty) {
          provided.text.trim

        } else {
          error(
            s"No $field string has been provided, either as a command line argument (--$field) or configuration file field.")
        }
      }
    }
  }

  private def resolveStringList(xml: NodeSeq): List[String] = {
    xml.text.split(',').map(_.trim).toList
  }

  private def resolveFallbackOptional(field: String,
                                      xml: NodeSeq,
                                      fallback: Option[String]) = {
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

  private def parsePipelineModifiers(xml: NodeSeq): PipelineModifiers = {
    PipelineModifiers(
      onlyVerify = false,
      onlyCompile = false,
      disableBaseline = false
    )
  }

  private def parseDB(xml: NodeSeq,
                      rootConfig: Config): BenchmarkDBCredentials = {
    val url = resolveFallback("url", xml, rootConfig.dbURLString)
    val username = resolveFallback("username", xml, rootConfig.dbUserString)
    val password = resolveFallback("password", xml, rootConfig.dbPassString)
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
        error(s"<$tag>: The specified directory $pathText doesn't exist.")
      }
    } catch {
      case _: InvalidPathException => {}
      error(s"<$tag>: Invalid path format: $pathText")
    }
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
      if (numberDefault == 0 && stress.isEmpty) {
        error(
          "No default stress configuration was provided, either as top-level <stress> under <workload> or the use of a wildcard ('*') in <match> under <by-program>")
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
      if (xml.text.matches("[0-9]+(,[0-9]+)+")) {
        Some(StressList(xml.text.split(',').map(s => s.trim.toInt).toList))
      } else {
        error(
          "Invalid input for <list>; expected a comma-separated list of integers"
        )
      }
    }
  }
}
