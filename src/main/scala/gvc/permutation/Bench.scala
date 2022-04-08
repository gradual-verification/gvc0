package gvc.permutation
import gvc.Main.verify
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.CapturedExecution.{
  CC0CompilationException,
  CapturedOutputException,
  ExecutionException
}
import gvc.permutation.Extensions.{c0, csv, log, out, txt}
import gvc.permutation.Output.blue
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.{Config, Main, OutputFileCollection, VerificationException}
import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
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

    val performance: String = csv("perf")
    val dynamicPerformance: String = csv("perf_full_dynamic")
    val framingPerformance: String = csv("perf_only_framing")

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
    Output.info(
      s"Saved ${benchConfig.prior.visitedPermutations.size} permutations from previous runs."
    )
    Output.info(
      s"Saved ${benchConfig.prior.visitedPaths.size} paths from previous runs."
    )
    if (!config.benchmarkSkipVerification) {
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
    var previousID: Option[String] = None
    val maxPaths = config.benchmarkPaths.getOrElse(1)
    val selector = new SelectVisitor(benchmarkConfig.ir)
    val csv =
      new MetadataCSVPrinter(benchmarkConfig.files, benchmarkConfig.labels)
    val err = new ErrorCSVPrinter(benchmarkConfig.files.verifyLogs)
    val sampler = new Sampler(benchmarkConfig)
    val progress =
      new VerificationTracker(benchmarkConfig.labels.length, maxPaths)

    def dumpPermutation(
        dir: Path,
        name: String,
        permutation: mutable.TreeSet[ASTLabel],
        sourceText: String
    ): Path = {
      val filePath = dir.resolve(name)
      Main.writeFile(
        filePath.toString,
        LabelTools.appendPathComment(sourceText, permutation.toList)
      )
      filePath
    }

    def generateBaseline(
        ir: IRGraph.Program,
        id: String,
        labels: mutable.TreeSet[ASTLabel],
        destDir: Path,
        onlyFraming: Boolean = false
    ): Unit = {
      BaselineChecker.check(ir, onlyFraming = onlyFraming)
      val dynamicSource =
        GraphPrinter.print(
          ir,
          includeSpecs = false
        )
      dumpPermutation(
        destDir,
        c0(id),
        labels,
        dynamicSource
      )
    }

    val bottomID =
      LabelTools.createID(benchmarkConfig.labels, Set.empty).toString(16)
    val outputBottom =
      benchmarkConfig.files.perms.resolve(c0(bottomID))
    val outputBottomVerified =
      benchmarkConfig.files.verifiedPerms.resolve(c0(bottomID))
    val outputBottomText =
      GraphPrinter.print(benchmarkConfig.ir, includeSpecs = false)
    Main.writeFile(
      outputBottom.toString,
      outputBottomText
    )
    Main.writeFile(
      outputBottomVerified.toString,
      outputBottomText
    )
    csv.logPermutation(
      bottomID,
      Set.empty
    )

    val offset = benchmarkConfig.prior.visitedPaths.size
    for (sampleIndex <- offset until maxPaths + offset) {
      val sampleToPermute =
        sampler.sample(SamplingHeuristic.Random)
      csv.logPath(sampleIndex, benchmarkConfig.labels, sampleToPermute)

      val summary = LabelTools.appendPathComment("", sampleToPermute)
      val summaryDestination =
        benchmarkConfig.files.pathDescriptions.resolve(
          txt(sampleIndex.toString)
        )
      Files.writeString(summaryDestination, summary)

      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()

      csv.logStep(bottomID, sampleIndex, 0, None)

      for (labelIndex <- sampleToPermute.indices) {
        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val id =
          LabelTools.createID(benchmarkConfig.labels, currentPermutation.toSet)
        val idString = id.toString(16)

        if (!alreadySampled.contains(id)) {
          csv.logPermutation(idString, currentPermutation.toSet)

          val builtPermutation = selector.visit(permutationIndices)
          val sourceText =
            GraphPrinter.print(builtPermutation, includeSpecs = true)
          dumpPermutation(
            benchmarkConfig.files.perms,
            c0(idString),
            currentPermutation,
            sourceText
          )
          try {
            val verifiedPermutation = config.timeout match {
              case Some(value) =>
                Timeout.runWithTimeout(value)(
                  verify(sourceText, outputFiles, config)
                )
              case None => Some(verify(sourceText, outputFiles, config))
            }
            verifiedPermutation match {
              case Some(vPerm) =>
                dumpPermutation(
                  benchmarkConfig.files.verifiedPerms,
                  c0(idString),
                  currentPermutation,
                  vPerm.c0Source
                )
                csv.logConjuncts(idString, vPerm.profiling)
                if (!config.disableBaseline) {
                  val builtDynamic = selector.visit(permutationIndices)
                  generateBaseline(
                    builtDynamic,
                    idString,
                    currentPermutation,
                    benchmarkConfig.files.dynamicPerms.get
                  )
                  val builtFraming = selector.visit(permutationIndices)
                  generateBaseline(
                    builtFraming,
                    idString,
                    currentPermutation,
                    benchmarkConfig.files.framingPerms.get,
                    onlyFraming = true
                  )
                }
              case None =>
            }
          } catch {
            case ex: VerificationException =>
              progress.error()
              err.log(idString, 1, ex.message)
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
          alreadySampled += id
          progress.incrementUnique()
        } else {
          progress.increment()
        }
        csv.logStep(
          idString,
          sampleIndex,
          labelIndex + 1,
          Some(sampleToPermute(labelIndex))
        )
        previousID = Some(idString)
      }
    }
    if (!config.disableBaseline) {
      val templateCopyDynamic = selector.visit(mutable.TreeSet[Int]())
      generateBaseline(
        templateCopyDynamic,
        bottomID,
        mutable.TreeSet[ASTLabel]()(LabelOrdering).empty,
        benchmarkConfig.files.dynamicPerms.get
      )
      val templateCopyFraming = selector.visit(mutable.TreeSet[Int]())
      generateBaseline(
        templateCopyFraming,
        bottomID,
        mutable.TreeSet[ASTLabel]()(LabelOrdering).empty,
        benchmarkConfig.files.framingPerms.get,
        onlyFraming = true
      )
    }
    csv.close()
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

    val printer = new PerformanceCSVPrinter(
      benchmarkConfig.files.performance,
      benchmarkConfig.workload.iterations
    )

    markDirectory(
      benchmarkConfig.files.verifiedPerms,
      printer,
      benchmarkConfig,
      ExecutionType.Gradual,
      ErrorLogging(errCC0, errExec)
    )

    if (!config.disableBaseline) {
      val framingPrinter = new PerformanceCSVPrinter(
        benchmarkConfig.files.framingPerformance,
        benchmarkConfig.workload.iterations
      )
      markDirectory(
        benchmarkConfig.files.framingPerms.get,
        framingPrinter,
        benchmarkConfig,
        ExecutionType.FramingOnly,
        ErrorLogging(errCC0, errExec)
      )

      val dynamicPrinter = new PerformanceCSVPrinter(
        benchmarkConfig.files.dynamicPerformance,
        benchmarkConfig.workload.iterations
      )
      markDirectory(
        benchmarkConfig.files.dynamicPerms.get,
        dynamicPrinter,
        benchmarkConfig,
        ExecutionType.FullDynamic,
        ErrorLogging(errCC0, errExec)
      )
    }
    if (Files.exists(Paths.get(Names.tempC0File)))
      Files.delete(Paths.get(Names.tempC0File))
    if (Files.exists(Paths.get(Names.tempBinaryFile)))
      Files.delete(Paths.get(Names.tempBinaryFile))
  }

  def markFile(
      in: Path,
      printer: PerformanceCSVPrinter,
      benchConfig: BenchmarkConfig,
      progressTracker: Option[ExecutionTracker] = None,
      logging: ErrorLogging
  ): Unit = {
    val id = Extensions.remove(in.getFileName.toString)
    val sourceString = Files.readString(in)
    val stepsRequired =
      printer.findMissingWorkloads(id, benchConfig.workload.stepList)

    if (stepsRequired.nonEmpty) {

      if (!isInjectable(sourceString)) {
        throw new BenchmarkException(
          s"The file ${in.getFileName} doesn't include an assignment of the form 'int stress = ...'."
        )
      }

      val source = injectStress(sourceString)

      val tempC0File = Paths.get(Names.tempC0File)
      val tempBinaryFile = Paths.get(Names.tempBinaryFile)
      Main.writeFile(
        tempC0File.toAbsolutePath.toString,
        source
      )
      try {
        CapturedExecution.compile(
          tempC0File,
          tempBinaryFile,
          benchConfig.rootConfig
        )

        for (workload <- stepsRequired) {
          val perf = CapturedExecution.exec_timed(
            tempBinaryFile,
            benchConfig.workload.iterations,
            List(s"--stress $workload")
          )
          printer.logID(id, workload, perf)
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
    }
    progressTracker match {
      case Some(value) => value.increment()
      case None        =>
    }
  }

  def markDirectory(
      in: Path,
      printer: PerformanceCSVPrinter,
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
