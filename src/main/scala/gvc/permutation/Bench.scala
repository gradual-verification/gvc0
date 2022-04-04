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
import gvc.transformer.GraphPrinter
import gvc.{Config, Main, OutputFileCollection, VerificationException}

import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.concurrent.TimeoutException
import scala.util.matching.Regex

object Bench {
  val firstAssign: Regex =
    "int[ ]+main\\(\\s*\\)\\s\\{.|\n*\n\\s*(stress\\s*=\\s*[0-9]+;)".r

  class BenchmarkException(message: String) extends Exception(message)

  object Names {
    val _baseline: String = c0("baseline")
    val perms = "perms"
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
      new VerificationTracker(benchmarkConfig.labels.length - 1, maxPaths)

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
      Set.empty
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
    csv.logPermutation(topID, benchmarkConfig.labels.toSet)
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

      csv.logStep(topID, sampleIndex, sampleToPermute.length)
      csv.logStep(bottomID, sampleIndex, 0)

      for (labelIndex <- 0 to sampleToPermute.length - 2) {

        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val id =
          LabelTools.createID(benchmarkConfig.labels, currentPermutation.toSet)
        val idString = id.toString(16)
        csv.logPermutation(idString, currentPermutation.toSet)

        if (!alreadySampled.contains(id)) {
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
        csv.logStep(idString, sampleIndex, labelIndex + 1)
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

  def markExecution(
      config: Config,
      benchmarkConfig: BenchmarkConfig
  ): Unit = {

    val printer = new PerformanceCSVPrinter(
      benchmarkConfig.files.performance,
      benchmarkConfig.workload.iterations
    )

    markDirectory(
      benchmarkConfig.files.verifiedPerms,
      printer,
      benchmarkConfig,
      ExecutionType.Gradual
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
        ExecutionType.Dynamic
      )
    }
  }

  def benchmarkFile(
      file: Path,
      stressLevel: Int,
      benchmarkConfig: BenchmarkConfig,
      printer: PerformanceCSVPrinter,
      progressTracker: Option[ExecutionTracker] = None
  ): Boolean = {
    val id = Extensions.remove(file.getFileName.toString)

    if (printer.exists(id, stressLevel)) return true

    val tempC0File = Paths.get(Names.tempC0File)
    val tempBinaryFile = Paths.get(Names.tempBinaryFile)

    val errCC0 = new ErrorCSVPrinter(benchmarkConfig.files.compilationLogs)
    val errExec = new ErrorCSVPrinter(benchmarkConfig.files.execLogs)
    val source = Files.readString(file)

    val unmodified = source
    val modified =
      source.replaceAll(firstAssign.toString(), s"\nstress = $stressLevel;")
    if (unmodified.equals(modified)) {
      Config.error(
        "Missing assignment of 'stress' variable in main."
      )
    }
    try {
      Main.writeFile(
        tempC0File.toAbsolutePath.toString,
        modified
      )
      val perf = CapturedExecution.compile_and_exec(
        tempC0File,
        tempBinaryFile,
        benchmarkConfig.workload.iterations,
        benchmarkConfig.rootConfig
      )
      printer.logID(id, stressLevel, perf)
    } catch {
      case co: CapturedOutputException =>
        co match {
          case cc0: CC0CompilationException =>
            cc0.logMessage(id, errCC0)
            progressTracker match {
              case Some(value) => value.cc0Error()
              case None        =>
            }
            return false
          case exec: ExecutionException =>
            exec.logMessage(id, errExec)
            progressTracker match {
              case Some(value) => value.execError()
              case None        =>
            }
            return false
        }
    } finally {
      if (Files.exists(tempC0File)) Files.delete(tempC0File)
      if (Files.exists(tempBinaryFile)) Files.delete(tempBinaryFile)

    }
    errCC0.close()
    errExec.close()
    true
  }

  def markFile(
      in: Path,
      printer: PerformanceCSVPrinter,
      benchConfig: BenchmarkConfig,
      progressTracker: Option[ExecutionTracker] = None
  ): Unit = {
    if (benchConfig.workload.wList.isEmpty) {
      for (
        i <- 0 to benchConfig.workload.wUpper by benchConfig.workload.wStep
      ) {
        val success =
          benchmarkFile(in, i, benchConfig, printer, progressTracker)
        if (!success) {
          progressTracker match {
            case Some(value) => value.increment()
            case None        =>
          }
          return
        }
      }
    } else {
      benchConfig.workload.wList.foreach(i => {
        val success =
          benchmarkFile(in, i, benchConfig, printer, progressTracker)
        if (!success) {
          progressTracker match {
            case Some(value) => value.increment()
            case None        =>
          }
          return
        }
      })
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
      verificationType: ExecutionType
  ): Unit = {
    val runlist = in.toFile
      .listFiles()
    if (runlist.nonEmpty) {
      val progress = new ExecutionTracker(runlist.length, verificationType)
      runlist.foreach(file => {
        markFile(file.toPath, printer, benchConfig, Some(progress))
      })
    } else {
      Output.error(s"No permutations to run in ${in.toString}.")
    }
  }
}
