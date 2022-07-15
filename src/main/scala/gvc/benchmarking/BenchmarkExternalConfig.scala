package gvc.benchmarking

import gvc.{Config, Main}
import gvc.Config.error
import gvc.benchmarking.BenchmarkSequential.Names
import gvc.benchmarking.Extensions.csv

import java.io.File
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
    nPaths: Int,
    stress: StressConfiguration
)

trait StressConfiguration

case class StressBounded(wLower: Int, wUpper: Int, wStep: Int)
    extends StressConfiguration

case class StressList(wList: List[Int]) extends StressConfiguration

case class StressSingular(stressValue: Int) extends StressConfiguration

case class PlatformIdentification(versionID: String, hardwareID: String)

case class SequentialConfig(io: SequentialOutputFiles,
                            workload: BenchmarkWorkload,
                            modifiers: PipelineModifiers)

case class PipelineModifiers(onlyVerify: Boolean,
                             onlyCompile: Boolean,
                             disableBaseline: Boolean)

case class PopulatorConfig(version: String,
                           pathQuantity: Int,
                           db: BenchmarkDBCredentials,
                           sources: List[Path])

case class ExecutorConfig(version: String,
                          hardware: String,
                          db: BenchmarkDBCredentials,
                          sourceDirectory: Path,
                          workload: BenchmarkWorkload)

object BenchmarkExternalConfig {

  def parseSequential(config: Config): SequentialConfig = {
    val sequentialConfigPath = config.sequentialConfig.get
    val xml = XML.loadFile(sequentialConfigPath.toFile)
    val sequentialRoot = xml \\ "sequential"
    if (sequentialRoot.isEmpty) {
      error("Expected <sequential> element.")
    } else {
      val source = sequentialRoot \ "source"
      val sourcePath = validateFile(source.text, "source")
      val outputDir = sequentialRoot \ "output-dir"
      val outputPath = validateDirectory(outputDir.text, "output-dir")
      val workload = parseWorkload(sequentialRoot)
      val pipelineModifiers = parsePipelineModifiers(sequentialRoot)
      val sequentialOutput =
        resolveSequentialOutputFiles(sourcePath,
                                     outputPath,
                                     pipelineModifiers,
                                     config)
      SequentialConfig(sequentialOutput, workload, pipelineModifiers)
    }
  }

  def parsePopulator(config: Config): PopulatorConfig = {
    val populatorConfigPath = config.populatorConfig.get
    val xml = XML.loadFile(populatorConfigPath.toFile)
    val populatorRoot = xml \\ "populator"
    if (populatorRoot.isEmpty) {
      error("Expected <populator> element.")
    } else {
      val version = resolveVersion(populatorRoot, config)
      val db = parseDB(populatorRoot)
      val quantity = intOrError(populatorRoot \ "quantity", "quantity")
      val sourceDirElement = populatorRoot \ "source-dir"
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
      PopulatorConfig(version, quantity, db, c0SourceFiles)
    }
  }

  def parseExecutor(config: Config): ExecutorConfig = {
    val executorConfigPath = config.executorConfig.get
    val xml = XML.loadFile(executorConfigPath.toFile)
    val executorRoot = xml \\ "executor"
    if (executorRoot.isEmpty) {
      error("Expected <executor> element.")
    } else {
      val versionString = resolveVersion(executorRoot, config)
      val hardware = executorRoot \ "hardware"
      val hardwareString = hardware.text
      if (hardwareString.trim.isEmpty) {
        error(s"<hardware>: Invalid hardware identifier: $hardwareString")
      }
      val workload = parseWorkload(executorRoot)
      val db = parseDB(executorRoot)
      val sources = executorRoot \ "source-dir"
      val validatedSources = validateDirectory(sources.text, "source-dir")
      ExecutorConfig(
        versionString,
        hardwareString,
        db,
        validatedSources,
        workload
      )
    }
  }

  private def resolveVersion(xml: NodeSeq, config: Config): String = {
    config.versionString match {
      case Some(value) => value
      case None =>
        val provided = xml \ "version"
        if (provided.nonEmpty) {
          provided.text
        } else {
          error(
            "No version string has been provided, either as a command line argument (--version) or configuration file field.")
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

  private def parseDB(xml: NodeSeq): BenchmarkDBCredentials = {
    val dbRoot = xml \\ "db"
    if (dbRoot.isEmpty) {
      error("Expected <db> credential tag.")
    } else {
      val url = dbRoot \ "url"
      val username = dbRoot \ "username"
      val passwordField = dbRoot \ "password"

      if (url.isEmpty || url.text.trim.isEmpty) {
        error("Missing <url> field in <db>")
      }
      if (username.isEmpty || url.text.trim.isEmpty) {
        error("Missing <username> field in <db>")
      }
      val password = if (passwordField.isEmpty) "" else passwordField.text
      BenchmarkDBCredentials(
        url.text,
        username.text,
        password,
      )
    }
  }

  private def intOrError(xml: NodeSeq, errorText: String): Int = {
    try {
      xml.text.toInt
    } catch {
      case _: NumberFormatException =>
        error(errorText)
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

  private def parseWorkload(xml: NodeSeq): BenchmarkWorkload = {
    val workloadRoot = xml \\ "workload"

    val paths = workloadRoot \ "paths"
    val iterations = workloadRoot \ "iterations"
    val iterQuantity =
      if (iterations.isEmpty) 1
      else
        intOrError(
          iterations,
          s"Expected an integer for <iterations>, but found: '${iterations.text}")

    val pathQuantity =
      if (paths.isEmpty) 1
      else
        intOrError(
          paths,
          s"Expected an integer for <paths>, but found: '${paths.text}'")

    val stress = workloadRoot \\ "stress"

    BenchmarkWorkload(pathQuantity, iterQuantity, parseStress(stress))
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
