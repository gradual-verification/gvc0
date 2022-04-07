package gvc.permutation
import gvc.Main.verify
import gvc.permutation.BenchConfig.BenchmarkConfig
import gvc.permutation.CapturedExecution.{CC0CompilationException, CapturedOutputException, ExecutionException}
import gvc.permutation.Extensions.{c0, csv, log, out, txt}
import gvc.permutation.Output.blue
import gvc.transformer.GraphPrinter
import gvc.{Config, Main, OutputFileCollection, VerificationException}
import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.concurrent.TimeoutException
import scala.util.matching.Regex

object Bench {
  val stressDeclaration: Regex = "int[ ]+main\\(\\s*\\)\\s\\{.|\n*\n\\s*(int stress = [0-9]+;)".r
  val stressAssignment: Regex =
    "int[ ]+main\\(\\s*\\)\\s\\{.|\n*\n\\s*(stress\\s*=\\s*[0-9]+;)".r
  class BenchmarkException(message: String) extends Exception(message)
  val readStress = "int readStress() {int* value = alloc(int); args_int(\"--stress\", value); args_t input = args_parse(); printint(*value); return *value;}\n"
  object Names {
    val _baseline: String = c0("baseline")
    val perms = "perms"
    val conjuncts = csv("conjuncts")
    val verified_perms = "verified_perms"
    val baselinePerms = "baseline_perms"
    val pathDesc = "path_desc"
    val performance: String = csv("perf")
    val baselinePerformance: String = csv("baseline_perf")
    val levels: String = csv("levels")
    val metadata: String = csv("metadata")
    val verifyLogs: String = log("verify")
    val compilationLogs: String = log("cc0")
    val baselineCompilationLogs: String = log("cc0_baseline")
    val execLogs: String = log("exec")
    val baselineExecLogs: String = log("exec_baseline")
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
    val bottomID =
      LabelTools.createID(benchmarkConfig.labels, Set.empty).toString(16)
    val outputBottom =
      benchmarkConfig.files.verifiedPerms.resolve(c0(bottomID))
    val outputBottomText =
      GraphPrinter.print(benchmarkConfig.ir, includeSpecs = false)
    Main.writeFile(
      outputBottom.toString,
      outputBottomText
    )
    csv.logPermutation(
      bottomID,
      Set.empty,
    )

    val topID =
      LabelTools
        .createID(benchmarkConfig.labels, benchmarkConfig.labels.toSet)
        .toString(16)
    val outputTop =
      benchmarkConfig.files.verifiedPerms.resolve(c0(topID))
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(benchmarkConfig.ir, includeSpecs = false)
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

      csv.logStep(topID, sampleIndex, sampleToPermute.length, Some(sampleToPermute.last))
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
                  val baselinePermutation = selector.visit(permutationIndices)
                  BaselineChecker.check(baselinePermutation)
                  val baselineSourceText =
                    GraphPrinter.print(
                      baselinePermutation,
                      includeSpecs = false
                    )
                  dumpPermutation(
                    benchmarkConfig.files.baselinePerms.get,
                    c0(idString),
                    currentPermutation,
                    baselineSourceText
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
        csv.logStep(idString, sampleIndex, labelIndex + 1, Some(sampleToPermute(labelIndex)))
        previousID = Some(idString)
      }
    }
    if (!config.disableBaseline) {
      BaselineChecker.check(benchmarkConfig.ir)
      val baselineSourceText =
        GraphPrinter.print(benchmarkConfig.ir, includeSpecs = false)
      dumpPermutation(
        benchmarkConfig.files.baselinePerms.get,
        c0(topID),
        mutable.TreeSet[ASTLabel]()(LabelOrdering),
        baselineSourceText
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

    val printer = new PerformanceCSVPrinter(
      benchmarkConfig.files.performance,
      benchmarkConfig.workload.iterations
    )
    val errCC0 = new ErrorCSVPrinter(benchmarkConfig.files.compilationLogs)
    val errExec = new ErrorCSVPrinter(benchmarkConfig.files.execLogs)

    markDirectory(
      benchmarkConfig.files.verifiedPerms,
      printer,
      benchmarkConfig,
      ExecutionType.Gradual,
      ErrorLogging(errCC0, errExec)
    )

    if (!config.disableBaseline) {
      val baselinePrinter = new PerformanceCSVPrinter(
        benchmarkConfig.files.baselinePerformance,
        benchmarkConfig.workload.iterations
      )
      markDirectory(
        benchmarkConfig.files.baselinePerms.get,
        baselinePrinter,
        benchmarkConfig,
        ExecutionType.Dynamic,
        ErrorLogging(errCC0, errExec)
      )
    }
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

    if(!isInjectable(sourceString)){
      throw new BenchmarkException(s"The file ${in.getFileName} doesn't include an assignment of the form 'int stress = ...'.")
    }
    val source = injectStress(sourceString)

    val tempC0File = Paths.get(Names.tempC0File)
    val tempBinaryFile = Paths.get(Names.tempBinaryFile)
    Main.writeFile(
      tempC0File.toAbsolutePath.toString,
      source
    )
    try {
      CapturedExecution.compile(tempC0File, tempBinaryFile, benchConfig.rootConfig)
      if (benchConfig.workload.wList.isEmpty) {
        for (i <- 0 to benchConfig.workload.wUpper by benchConfig.workload.wStep) {
          val perf = CapturedExecution.exec_timed(tempBinaryFile, benchConfig.workload.iterations, List(s"--stress $i"))
          printer.logID(id, i, perf)
        }
      } else {
        for(i <- benchConfig.workload.wList)  {
          val perf = CapturedExecution.exec_timed(tempBinaryFile, benchConfig.workload.iterations, List(s"--stress $i"))
          printer.logID(id, i, perf)
        }
      }
    }catch {
      case c0: CapturedOutputException =>
        c0 match {
          case cc0: CC0CompilationException =>
            cc0.logMessage(id, logging.cc0)
            progressTracker match {
              case Some(value) => value.cc0Error()
              case None =>
            }
          case exec: ExecutionException =>
            exec.logMessage(id, logging.exec)
            progressTracker match {
              case Some(value) => value.execError()
              case None =>
            }
        }
    }
    progressTracker match {
      case Some(value) => value.increment()
      case None        =>
    }
    if (Files.exists(tempC0File)) Files.delete(tempC0File)
    if (Files.exists(tempBinaryFile)) Files.delete(tempBinaryFile)
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
    val withoutDeclarations = stressAssignment.replaceAllIn(source, "")
    val withStressDeclaration = stressDeclaration.replaceAllIn(withoutDeclarations, "int stress = readStress();")
    "#use <conio>\n#use <args>\n" + withStressDeclaration + readStress
  }

  def isInjectable(source: String): Boolean = {
    stressAssignment.findAllMatchIn(source).nonEmpty && stressDeclaration.findAllMatchIn(source).nonEmpty
  }
}