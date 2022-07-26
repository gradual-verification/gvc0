package gvc.benchmarking

import gvc.{Config, Main}
import gvc.Config.error
import gvc.benchmarking.Benchmark.Names
import gvc.benchmarking.Extensions.csv
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
    stress: StressConfiguration
)

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

case class PopulatorConfig(version: String,
                           pathQuantity: Option[Int],
                           db: BenchmarkDBCredentials,
                           sources: List[Path])
    extends BenchmarkingConfig

case class ExecutorConfig(version: String,
                          hardware: String,
                          nickname: Option[String],
                          db: BenchmarkDBCredentials,
                          sources: List[Path],
                          workload: BenchmarkWorkload)
    extends BenchmarkingConfig

case class BenchmarkConfigResults(
    version: String,
    hardware: String,
    nickname: Option[String],
    credentials: BenchmarkDBCredentials,
    sources: List[Path],
    workload: Option[BenchmarkWorkload],
    pathQuantity: Option[Int],
    modifiers: PipelineModifiers
)

object BenchmarkExternalConfig {

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
    resolved.workload match {
      case Some(value) =>
        ExecutorConfig(
          resolved.version,
          resolved.hardware,
          resolved.nickname,
          resolved.credentials,
          resolved.sources,
          value
        )
      case None => error("A <workload> must be provided.")
    }
  }

  def parsePopulator(rootConfig: Config): PopulatorConfig = {
    val resolved = parseConfig(rootConfig)
    PopulatorConfig(resolved.version,
                    resolved.pathQuantity,
                    resolved.credentials,
                    resolved.sources)
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
        resolveFallback("hardware", benchmarkRoot, rootConfig.hardwareString)
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

      val credentials = parseDB(benchmarkRoot \\ "db", rootConfig)

      val workload = parseWorkload(benchmarkRoot \\ "workload")

      val modifiers = parsePipelineModifiers(benchmarkRoot)

      BenchmarkConfigResults(version,
                             hardware,
                             nickname,
                             credentials,
                             fileCollection,
                             workload,
                             quantity,
                             modifiers)
    }
  }

  def generateStressList(stress: StressConfiguration): List[Int] = {
    val stepList = stress match {
      case singular: StressSingular => List(singular.stressValue)
      case list: StressList         => list.wList
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

  private def parseWorkload(xml: NodeSeq): Option[BenchmarkWorkload] = {
    val workloadRoot = xml \\ "workload"
    if (workloadRoot.isEmpty) {
      None
    } else {
      val paths = workloadRoot \ "paths"
      val iterations = workloadRoot \ "iterations"
      val staticIterations = workloadRoot \ "static-iterations"
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
      val stress = workloadRoot \\ "stress"
      Some(
        BenchmarkWorkload(iterQuantity,
                          staticIterQuantity,
                          pathQuantity,
                          parseStress(stress)))
    }
  }

  private def parseStress(xml: NodeSeq): StressConfiguration = {
    val listed = parseStressListed(xml \ "list")
    val singular = parseStressSingular(xml \ "singular")
    val bounded = parseStressBounded(xml \ "bounded")

    val specified = List(listed, singular, bounded).filter(_.nonEmpty)
    if (specified.length > 1) {
      error(
        "Only one workload specification method can be used for <stress>; multiple were found.")
    } else {
      specified.head match {
        case Some(value) => value
        case None =>
          error("Missing workload specification under <stress>")
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

  private def resolveSequentialOutputFiles(
      inputSource: java.nio.file.Path,
      root: java.nio.file.Path,
      modifiers: PipelineModifiers,
      config: Config
  ): SequentialOutputFiles = {
    def deleteMultiple(locations: java.nio.file.Path*): Unit =
      locations.foreach(p => {
        Files.deleteIfExists(p)
      })

    val disableBaseline = modifiers.disableBaseline

    Files.createDirectories(root)

    val existingSource = root.resolve(Names.source)

    if (Files.exists(existingSource)) {
      if (!Files
            .readString(existingSource)
            .equals(Files.readString(inputSource)))
        Config.error(
          s"The existing permutation directory ${existingSource.getParent.toAbsolutePath} was created for a different source file than the one provided"
        )
    } else {
      Main.writeFile(existingSource.toString, inputSource.toString)
    }

    val perms = root.resolve(Names.perms)
    Files.createDirectories(perms)

    val verifiedPerms = root.resolve(Names.verifiedPerms)
    Files.createDirectories(verifiedPerms)

    val dynamicPerms: Option[java.nio.file.Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.dynamicPerms)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val framingPerms: Option[java.nio.file.Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.framingPerms)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val pathDescriptions = root.resolve(Names.pathDesc)
    Files.createDirectories(pathDescriptions)

    val executionPerformanceGradual =
      root.resolve(Names.executionPerformanceGradual)
    val executionPerformanceDynamic =
      root.resolve(Names.executionPerformanceDynamic)
    val executionPerformanceFraming =
      root.resolve(Names.executionPerformanceFraming)

    val instrumentationPerformance =
      root.resolve(Names.instrumentationPerformance)
    val verificationPerformance = root.resolve(Names.verificationPerformance)

    val compilationPerformanceGradual =
      root.resolve(Names.compilationPerformanceGradual)
    val compilationPerformanceDynamic =
      root.resolve(Names.compilationPerformanceDynamic)
    val compilationPerformanceFraming =
      root.resolve(Names.compilationPerformanceFraming)

    val translationPerformance = root.resolve(Names.translationPerformance)

    if (config.onlyExec) {
      deleteMultiple(
        executionPerformanceGradual,
        executionPerformanceDynamic,
        executionPerformanceFraming,
        compilationPerformanceFraming,
        compilationPerformanceDynamic,
        compilationPerformanceGradual
      )
    } else if (config.onlyVerify) {
      deleteMultiple(verificationPerformance, instrumentationPerformance)
    } else {
      deleteMultiple(
        executionPerformanceGradual,
        executionPerformanceDynamic,
        executionPerformanceFraming,
        verificationPerformance,
        instrumentationPerformance,
        compilationPerformanceFraming,
        compilationPerformanceDynamic,
        compilationPerformanceGradual
      )
    }

    val logs = root.resolve(Names.logs)
    Files.createDirectories(logs)
    val verifyLog = logs.resolve(Names.verifyLogs)
    val compileLog = logs.resolve(Names.compilationLogs)
    val dynamicCompileLog = logs.resolve(Names.dynamicCompilationLogs)
    val framingCompileLog = logs.resolve(Names.framingCompilationLogs)
    val exec = logs.resolve(Names.execLogs)
    val dynamicExecLog = logs.resolve(Names.dynamicExecLogs)
    val framingExecLog = logs.resolve(Names.framingExecLogs)
    deleteMultiple(
      compileLog,
      dynamicCompileLog,
      framingCompileLog,
      verifyLog,
      exec,
      dynamicExecLog,
      framingExecLog
    )

    val levels = root.resolve(Names.levels)
    val metadata = root.resolve(Names.metadata)
    val permMap = root.resolve(csv(Names.perms))
    val conjunctMap = root.resolve(Names.conjuncts)
    if (!config.onlyExec) {
      deleteMultiple(levels, metadata, permMap, conjunctMap)
    }

    val tempC0File = Files.createTempFile("", Names.tempC0File)
    val tempBinaryFile = Files.createTempFile("", Names.tempBinaryFile)

    SequentialOutputFiles(
      root = root,
      perms = perms,
      verifiedPerms = verifiedPerms,
      dynamicPerms = dynamicPerms,
      logs = logs,
      verifyLogs = verifyLog,
      compilationLogs = compileLog,
      dynamicCompilationLogs = dynamicCompileLog,
      execLogs = exec,
      dynamicExecLogs = dynamicExecLog,
      levels = levels,
      metadata = metadata,
      pathDescriptions = pathDescriptions,
      source = existingSource,
      permMap = permMap,
      conjunctMap = conjunctMap,
      framingExecLogs = framingExecLog,
      framingCompilationLogs = framingCompileLog,
      framingPerms = framingPerms,
      tempC0File = tempC0File,
      tempBinaryFile = tempBinaryFile,
      verificationPerformance = verificationPerformance,
      instrumentationPerformance = instrumentationPerformance,
      //
      compilationPerformanceGradual = compilationPerformanceGradual,
      compilationPerformanceDynamic = compilationPerformanceDynamic,
      compilationPerformanceFraming = compilationPerformanceFraming,
      //
      executionPerformanceGradual = executionPerformanceGradual,
      executionPerformanceDynamic = executionPerformanceDynamic,
      executionPerformanceFraming = executionPerformanceFraming,
      //
      translationPerformance = translationPerformance
    )
  }
}

case class SequentialOutputFiles(
    root: java.nio.file.Path,
    perms: java.nio.file.Path,
    verifiedPerms: java.nio.file.Path,
    pathDescriptions: java.nio.file.Path,
    dynamicPerms: Option[java.nio.file.Path],
    framingPerms: Option[java.nio.file.Path],
    logs: java.nio.file.Path,
    verifyLogs: java.nio.file.Path,
    //
    compilationLogs: java.nio.file.Path,
    dynamicCompilationLogs: java.nio.file.Path,
    framingCompilationLogs: java.nio.file.Path,
    //
    execLogs: java.nio.file.Path,
    dynamicExecLogs: java.nio.file.Path,
    framingExecLogs: java.nio.file.Path,
    //
    verificationPerformance: java.nio.file.Path,
    instrumentationPerformance: java.nio.file.Path,
    translationPerformance: java.nio.file.Path,
    //
    compilationPerformanceGradual: java.nio.file.Path,
    compilationPerformanceDynamic: java.nio.file.Path,
    compilationPerformanceFraming: java.nio.file.Path,
    //
    executionPerformanceGradual: java.nio.file.Path,
    executionPerformanceDynamic: java.nio.file.Path,
    executionPerformanceFraming: java.nio.file.Path,
    //
    levels: java.nio.file.Path,
    metadata: java.nio.file.Path,
    source: java.nio.file.Path,
    permMap: java.nio.file.Path,
    conjunctMap: java.nio.file.Path,
    //
    tempC0File: java.nio.file.Path,
    tempBinaryFile: java.nio.file.Path
)
