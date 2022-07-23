package gvc.permutation
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.Extensions.{c0, csv, log, out, txt}
import gvc.permutation.Output.blue
import gvc.permutation.Timing.{
  CC0CompilationException,
  CapturedOutputException,
  ExecutionException
}
import gvc.transformer.{IR, IRPrinter}
import gvc.{Config, Main, OutputFileCollection, VerificationException}

import java.math.BigInteger
import java.nio.file.{Files, Path}
import scala.collection.mutable
import scala.concurrent.TimeoutException
import scala.util.matching.Regex

object Bench {
  val arbitraryStressDeclaration: Regex = "(int )?(stress = [0-9]+;)".r
  val correctStressDeclaration: Regex =
    "(int[ ]+main\\(\\s*\\)\\s\\{[\\s\\S]*\n\\s*int stress = [0-9]+;)".r
  class BenchmarkException(message: String) extends Exception(message)
  val readStress =
    "int readStress() {int* value = alloc(int); args_int(\"--stress\", value); args_t input = args_parse(); printint(*value); return *value;}\n"
  object Names {
    val conjuncts: String = csv("conjuncts")
    //
    val perms = "perms"
    val verifiedPerms = "perms_verified"
    val dynamicPerms = "perms_full_dynamic"
    val framingPerms = "perms_only_framing"
    //
    val pathDesc = "path_desc"

    val executionPerformanceGradual: String = csv("dyn_perf_gradual")
    val executionPerformanceDynamic: String = csv("dyn_perf_full_dynamic")
    val executionPerformanceFraming: String = csv("dyn_perf_only_framing")

    val verificationPerformance: String = csv("verification_perf")
    val instrumentationPerformance: String = csv("instrumentation_perf")

    val compilationPerformanceGradual: String = csv("compilation_perf_gradual")
    val compilationPerformanceDynamic: String = csv(
      "compilation_perf_full_dynamic"
    )
    val compilationPerformanceFraming: String = csv(
      "compilation_perf_only_framing"
    )
    val translationPerformance: String = csv("translation_perf")

    val levels: String = csv("levels")
    val metadata: String = csv("metadata")
    //
    val verifyLogs: String = log("verify")
    val compilationLogs: String = log("cc0")
    val dynamicCompilationLogs: String = log("cc0_full_dynamic")
    val framingCompilationLogs: String = log("cc0_only_framing")
    //
    val execLogs: String = log("exec")
    val dynamicExecLogs: String = log("exec_full_dynamic")
    val framingExecLogs: String = log("exec_only_framing")
    //
    val source: String = c0("source")
    val logs = "logs"
    val stressDeclaration = "stress"
    val entry = "main"
    val tempC0File: String = c0("temp")
    val tempBinaryFile: String = out("temp")
  }

  def mark(
      source: String,
      config: Config,
      outputFiles: OutputFileCollection,
      librarySearchDirs: List[String]
  ): Unit = {
    val file = c0(outputFiles.baseName)
    val benchConfig =
      BenchConfig.resolveBenchmarkConfig(source, librarySearchDirs, config)

    if (!config.onlyExec && !config.onlyCompile) {
      val timeout = config.timeout match {
        case Some(value) => value.toString + "s"
        case None        => "infinite"
      }
      val paths = benchConfig.workload.nPaths
      val pathDesc =
        s"${Output.blue(paths.toString)} path" +
          (if (paths > 1) "s" else "")
      val iterations = benchConfig.workload.iterations
      val iterDesc =
        if (config.onlyVerify) ""
        else
          s" with ${Output.blue(iterations.toString)} iteration" +
            (if (iterations > 1) "s" else "") + " per permutation"

      Output.info(
        s"Benchmarking $pathDesc$iterDesc for ${blue(
          file
        )}, timeout ${blue(timeout)}, output to ${blue(benchConfig.files.root.toString)}"
      )

      def booleanToStatus(a: Boolean): String =
        if (a) Output.green("enabled") else Output.red("disabled")

      Output.info(
        s"Baseline ${booleanToStatus(!config.disableBaseline)}, execution ${booleanToStatus(!config.onlyVerify)}"
      )

      markVerification(
        config,
        outputFiles,
        benchConfig
      )
      println(s"${Output.formatSuccess("Verification completed.")}")
    }
    if (!config.onlyVerify) {
      markExecution(config, benchConfig)
      print(
        s"\n\n${Output.formatSuccess("Compilation & Execution completed.")}\n"
      )
    } else {
      print(
        s"\n${Output.formatSuccess("Benchmarking completed.")}\n"
      )
    }
  }

  def markVerification(
      config: Config,
      outputFiles: OutputFileCollection,
      benchmarkConfig: BenchmarkConfig
  ): Unit = {

    val alreadySampled: mutable.Set[BigInteger] =
      mutable.Set[BigInteger]()
    val maxPaths = config.benchmarkPaths.getOrElse(1)
    val metaCSV =
      new MetadataCSVPrinter(
        benchmarkConfig.files,
        benchmarkConfig.labelOutput.labels
      )
    val staticCSV =
      new StaticCSVPrinter(benchmarkConfig)

    val err = new ErrorCSVPrinter(benchmarkConfig.files.verifyLogs)

    val sampler = new Sampler(benchmarkConfig)

    val progress =
      new VerificationTracker(
        benchmarkConfig.labelOutput.labels.length,
        maxPaths
      )

    def dumpPermutation(
        dir: Path,
        name: String,
        permutation: List[ASTLabel],
        sourceText: String
    ): Path = {
      val filePath = dir.resolve(name)
      Main.writeFile(
        filePath.toString,
        LabelTools.appendPathComment(sourceText, permutation)
      )
      filePath
    }

    def generateBaseline(
        ir: IR.Program,
        id: BigInteger,
        labels: List[ASTLabel],
        destDir: Path,
        onlyFraming: Boolean = false
    ): Unit = {

      BaselineChecker.check(ir, onlyFraming = onlyFraming)
      val dynamicSource =
        IRPrinter.print(
          ir,
          includeSpecs = false
        )
      dumpPermutation(
        destDir,
        c0(id.toString(16)),
        labels,
        dynamicSource
      )
    }

    def verifyPermutation(
        visitor: SelectVisitor,
        id: BigInteger,
        currentPermutation: LabelPermutation
    ): Unit = {

      val idString = id.toString(16)
      metaCSV.logPermutation(idString, currentPermutation)
      val builtPermutation =
        visitor.visit(currentPermutation)
      val sourceText =
        IRPrinter.print(builtPermutation, includeSpecs = true)
      dumpPermutation(
        benchmarkConfig.files.perms,
        c0(idString),
        currentPermutation.labels,
        sourceText
      )
      try {
        val verifiedPermutation = config.timeout match {
          case Some(value) =>
            Timeout.runWithTimeout(value)(
              Timing.verifyTimed(sourceText, outputFiles, benchmarkConfig)
            )
          case None =>
            Some(Timing.verifyTimed(sourceText, outputFiles, benchmarkConfig))
        }
        verifiedPermutation match {
          case Some(verifierOutput) =>
            staticCSV.log(idString, verifierOutput)
            val info = verifierOutput.output
            dumpPermutation(
              benchmarkConfig.files.verifiedPerms,
              c0(idString),
              currentPermutation.labels,
              info.c0Source
            )
            metaCSV.logConjuncts(idString, info.profiling)
            if (!config.disableBaseline) {
              val builtDynamic = new SelectVisitor(benchmarkConfig.ir)
                .visit(currentPermutation)
              generateBaseline(
                builtDynamic,
                id,
                currentPermutation.labels,
                benchmarkConfig.files.dynamicPerms.get
              )
              val builtFraming = new SelectVisitor(benchmarkConfig.ir)
                .visit(currentPermutation)
              generateBaseline(
                builtFraming,
                id,
                currentPermutation.labels,
                benchmarkConfig.files.framingPerms.get,
                onlyFraming = true
              )
            }
          case None =>
        }
      } catch {
        case ex: VerificationException =>
          progress.error()
          err.log(idString, exitCode = 1, ex.message)
        case _: TimeoutException =>
          progress.timeout()
          val message =
            s"\n\n ---[Timeout after ${config.timeout.get} ms]---\n"
          println(message)
          err.log(
            idString,
            exitCode = 1,
            message
          )
      }
    }

    val bottomID = new LabelPermutation(benchmarkConfig).id
    val outputBottom =
      benchmarkConfig.files.perms.resolve(c0(bottomID))
    val outputBottomVerified =
      benchmarkConfig.files.verifiedPerms.resolve(c0(bottomID))
    val outputBottomText =
      IRPrinter.print(benchmarkConfig.ir, includeSpecs = false)
    Main.writeFile(
      outputBottom.toString,
      outputBottomText
    )
    Main.writeFile(
      outputBottomVerified.toString,
      outputBottomText
    )
    metaCSV.logPermutation(
      bottomID.toString(16),
      new LabelPermutation(benchmarkConfig)
    )
    val visitor = new SelectVisitor(benchmarkConfig.ir)

    for (pathIndex <- 0 until maxPaths) {
      val sampleToPermute =
        sampler.sample(SamplingHeuristic.Random)

      metaCSV.logPath(
        pathIndex,
        benchmarkConfig.labelOutput.labels,
        sampleToPermute
      )
      val summary = LabelTools.appendPathComment("", sampleToPermute)
      val summaryDestination =
        benchmarkConfig.files.pathDescriptions.resolve(
          txt(pathIndex.toString)
        )
      Files.writeString(summaryDestination, summary)

      metaCSV.logStep(bottomID, pathIndex, 0, None)
      val currentPermutation = new LabelPermutation(benchmarkConfig)

      for (labelIndex <- sampleToPermute.indices) {
        currentPermutation.addLabel(sampleToPermute(labelIndex))
        val id = currentPermutation.id
        if (!alreadySampled.contains(id)) {
          progress.incrementUnique()
          verifyPermutation(visitor, id, currentPermutation)
          alreadySampled += id
        } else {
          progress.increment()
        }
        metaCSV.logStep(
          id,
          pathIndex,
          labelIndex + 1,
          Some(sampleToPermute(labelIndex))
        )
      }
    }
    if (sampler.numSampled != maxPaths) {
      throw new BenchmarkException(
        "Failed to sample the requested quantity of paths; " + sampler.numSampled + "!=" + maxPaths
      )
    }
    if (!config.disableBaseline) {
      val templateCopyDynamic =
        new SelectVisitor(benchmarkConfig.ir).visitEmpty()
      generateBaseline(
        templateCopyDynamic,
        bottomID,
        List.empty,
        benchmarkConfig.files.dynamicPerms.get
      )
      val templateCopyFraming =
        new SelectVisitor(benchmarkConfig.ir).visitEmpty()
      generateBaseline(
        templateCopyFraming,
        bottomID,
        List.empty,
        benchmarkConfig.files.framingPerms.get,
        onlyFraming = true
      )
    }
    metaCSV.close()
    staticCSV.close()
    err.close()
  }
  sealed trait Stress
  case class StressList(levels: List[Int]) extends Stress
  case class StressScaling(stepSize: Int, upperBound: Int) extends Stress
  case class ErrorLogging(cc0: ErrorCSVPrinter, exec: ErrorCSVPrinter)

  def markExecution(
      config: Config,
      benchmarkConfig: BenchmarkConfig
  ): Unit = {

    val errCC0 = new ErrorCSVPrinter(benchmarkConfig.files.compilationLogs)
    val errExec = new ErrorCSVPrinter(benchmarkConfig.files.execLogs)

    val printer = new DynamicCSVPrinter(
      benchmarkConfig,
      ExecutionType.Gradual
    )
    /*
    markDirectory(
      benchmarkConfig.files.verifiedPerms,
      printer,
      benchmarkConfig,
      ExecutionType.Gradual,
      ErrorLogging(errCC0, errExec)
    )*/
    printer.close()

    if (!config.disableBaseline) {
      val framingPrinter = new DynamicCSVPrinter(
        benchmarkConfig,
        ExecutionType.FramingOnly
      )

      markDirectory(
        benchmarkConfig.files.framingPerms.get,
        framingPrinter,
        benchmarkConfig,
        ExecutionType.FramingOnly,
        ErrorLogging(errCC0, errExec)
      )

      framingPrinter.close()

      val dynamicPrinter = new DynamicCSVPrinter(
        benchmarkConfig,
        ExecutionType.FullDynamic
      )

      markDirectory(
        benchmarkConfig.files.dynamicPerms.get,
        dynamicPrinter,
        benchmarkConfig,
        ExecutionType.FullDynamic,
        ErrorLogging(errCC0, errExec)
      )

      dynamicPrinter.close()
    }
    if (Files.exists(benchmarkConfig.files.tempC0File))
      Files.delete(benchmarkConfig.files.tempC0File)
    if (Files.exists(benchmarkConfig.files.tempBinaryFile))
      Files.delete(benchmarkConfig.files.tempBinaryFile)
  }

  def markFile(
      in: Path,
      printer: DynamicCSVPrinter,
      benchConfig: BenchmarkConfig,
      progressTracker: Option[ExecutionTracker] = None,
      logging: ErrorLogging
  ): Unit = {
    val id = Extensions.remove(in.getFileName.toString)
    val sourceString = Files.readString(in)

    if (!isInjectable(sourceString)) {
      throw new BenchmarkException(
        s"The file ${in.getFileName} doesn't include an assignment of the form 'int stress = ...'."
      )
    }

    val source = injectStress(sourceString)

    Main.writeFile(
      benchConfig.files.tempC0File.toAbsolutePath.toString,
      source
    )
    try {
      val perfComp = Timing.compileTimed(
        benchConfig.files.tempC0File,
        benchConfig.files.tempBinaryFile,
        benchConfig
      )
      printer.logCompilation(id, perfComp)

      if (!benchConfig.rootConfig.onlyCompile) {
        for (workload <- benchConfig.workload.stepList) {
          val perf = Timing.execTimed(
            benchConfig.files.tempBinaryFile,
            benchConfig.workload.iterations,
            List(s"--stress $workload")
          )
          printer.logExecution(id, workload, perf)
        }
      }
    } catch {
      case c0: CapturedOutputException =>
        c0 match {
          case cc0: CC0CompilationException =>
            cc0.logMessage(id, logging.cc0)
            progressTracker match {
              case Some(value) => value.cc0Error()
              case None        =>
            }
          case exec: ExecutionException =>
            exec.logMessage(id, logging.exec)
            progressTracker match {
              case Some(value) => value.execError()
              case None        =>
            }
        }
    }
    progressTracker match {
      case Some(value) => value.increment()
      case None        =>
    }
  }

  def markDirectory(
      in: Path,
      printer: DynamicCSVPrinter,
      benchConfig: BenchmarkConfig,
      verificationType: ExecutionType,
      logging: ErrorLogging
  ): Unit = {
    val runlist = in.toFile
      .listFiles()
    if (runlist.nonEmpty) {
      val progress = new ExecutionTracker(runlist.length, verificationType)
      runlist.foreach(file => {
        markFile(file.toPath, printer, benchConfig, Some(progress), logging)
      })
    } else {
      Output.error(s"No permutations to run in ${in.toString}.")
    }
  }

  def injectStress(source: String): String = {
    val withStressDeclaration = correctStressDeclaration.replaceFirstIn(
      source,
      readStress + "int main()\n{\nint stress = readStress();\n"
    )
    val removedAdditionalAssignments =
      arbitraryStressDeclaration.replaceAllIn(withStressDeclaration, "")
    "#use <conio>\n#use <args>\n" + removedAdditionalAssignments
  }
  def isInjectable(source: String): Boolean = {
    correctStressDeclaration
      .findAllMatchIn(source)
      .nonEmpty
  }
}
