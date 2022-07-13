package gvc.permutation

import gvc.{Config, Main}
import gvc.permutation.Bench.Names
import gvc.permutation.Extensions.csv
import gvc.transformer.IR

import java.nio.file.{Files, Path, Paths}

object BenchConfig {

  case class BenchmarkConfig(
      files: BenchmarkOutputFiles,
      workload: BenchmarkWorkload,
      ir: IR.Program,
      labelOutput: LabelOutput,
      rootConfig: Config
  )

  case class BenchmarkWorkload(
      iterations: Int,
      wUpper: Int,
      wStep: Int,
      wList: List[Int],
      nPaths: Int,
      stepList: List[Int]
  )

  case class BenchmarkOutputFiles(
      root: Path,
      perms: Path,
      verifiedPerms: Path,
      pathDescriptions: Path,
      dynamicPerms: Option[Path],
      framingPerms: Option[Path],
      logs: Path,
      verifyLogs: Path,
      //
      compilationLogs: Path,
      dynamicCompilationLogs: Path,
      framingCompilationLogs: Path,
      //
      execLogs: Path,
      dynamicExecLogs: Path,
      framingExecLogs: Path,
      //
      verificationPerformance: Path,
      instrumentationPerformance: Path,
      translationPerformance: Path,
      //
      compilationPerformanceGradual: Path,
      compilationPerformanceDynamic: Path,
      compilationPerformanceFraming: Path,
      //
      executionPerformanceGradual: Path,
      executionPerformanceDynamic: Path,
      executionPerformanceFraming: Path,
      //
      levels: Path,
      metadata: Path,
      source: Path,
      permMap: Path,
      conjunctMap: Path,
      //
      tempC0File: Path,
      tempBinaryFile: Path
  )

  private def deleteMultiple(locations: Path*): Unit =
    locations.foreach(p => {
      Files.deleteIfExists(p)
    })

  private def resolveOutputFiles(
      inputSource: String,
      config: Config
  ): BenchmarkOutputFiles = {
    val dir = config.compileBenchmark.get
    val disableBaseline = config.disableBaseline

    val root = Paths.get(dir)
    Files.createDirectories(root)

    val existingSource = root.resolve(Names.source)

    if (Files.exists(existingSource)) {
      if (!Files.readString(existingSource).equals(inputSource))
        Config.error(
          s"The existing permutation directory ${existingSource.getParent.toAbsolutePath} was created for a different source file than the one provided"
        )
    } else {
      Main.writeFile(existingSource.toString, inputSource)
    }

    val perms = root.resolve(Names.perms)
    Files.createDirectories(perms)

    val verifiedPerms = root.resolve(Names.verifiedPerms)
    Files.createDirectories(verifiedPerms)

    val dynamicPerms: Option[Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.dynamicPerms)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val framingPerms: Option[Path] = if (!disableBaseline) {
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

    BenchmarkOutputFiles(
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

  def resolveWorkload(config: Config): BenchmarkWorkload = {
    val step = config.benchmarkWStep.getOrElse(8)
    val upper = config.benchmarkWUpper.getOrElse(32)
    val stepList = config.benchmarkWList match {
      case Some(value) => value
      case None        => for (i <- 0 to upper by step) yield i
    }
    BenchmarkWorkload(
      config.benchmarkIterations.getOrElse(1),
      config.benchmarkWUpper.getOrElse(32),
      config.benchmarkWStep.getOrElse(8),
      config.benchmarkWList.getOrElse(List()),
      config.benchmarkPaths.getOrElse(1),
      stepList.toList
    )
  }

  def resolveBenchmarkConfig(
      source: String,
      librarySearchPaths: List[String],
      config: Config
  ): BenchmarkConfig = {
    val ir = Main.generateIR(source, librarySearchPaths)
    val labeler = new LabelVisitor()
    val labels = labeler.visit(ir)
    val files = resolveOutputFiles(source, config)
    val work = resolveWorkload(config)
    BenchmarkConfig(
      files = files,
      ir = ir,
      labelOutput = labels,
      workload = work,
      rootConfig = config
    )
  }
}
