package gvc.permutation
import gvc.Main.verify
import gvc.permutation.CapturedExecution.{
  CC0CompilationException,
  CapturedOutputException,
  ExecutionException
}
import gvc.permutation.Output.blue
import gvc.transformer.GraphPrinter
import gvc.{Config, Main, OutputFileCollection, VerificationException}
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.concurrent.TimeoutException
import scala.reflect.io.Directory
import scala.language.postfixOps
import scala.util.matching.Regex

object Bench {
  private val assign: Regex = "(int[ ]+stress[ ]*=[ ]*[0-9]+[ ]*;)".r
  private val firstAssign: Regex =
    "(int[ ]+main[ ]*\\([ ]*\\)\\s*\\{\\s*int[ ]+stress[ ]*=[ ]*[0-9]+[ ]*;)".r

  class BenchmarkException(message: String) extends Exception(message)

  def c0(basename: String): String = basename + ".c0"

  def out(basename: String): String = basename + ".out"

  def csv(basename: String): String = basename + ".csv"

  def log(basename: String): String = basename + ".log"

  case class BenchmarkOutputFiles(
      root: Path,
      perms: Path,
      verifiedPerms: Path,
      baselinePerms: Option[Path],
      logs: Path,
      verifyLogs: Path,
      baselineCompilationLogs: Path,
      execLogs: Path,
      baselineExecLogs: Path,
      compilationLogs: Path,
      performance: Path,
      baselinePerformance: Path,
      levels: Path,
      metadata: Path
  )

  object Names {
    val _baseline: String = c0("baseline")
    val _top = "top"
    val _bottom = "bot"
    val perms = "perms"
    val verified_perms = "verified_perms"
    val baselinePerms = "baseline_perms"
    val performance = "performance"
    val baselinePerformance = "baselinePerformance"
    val levels: String = csv("levels")
    val metadata: String = csv("metadata")
    val verifyLogs: String = log("verify")

    val compilationLogs: String = log("cc0")
    val baselineCompilationLogs: String = log("cc0_baseline")
    val execLogs: String = log("exec")
    val baselineExecLogs: String = log("exec_baseline")

    val logs = "logs"
    val stressDeclaration = "stress"
    val entry = "main"
    val tempC0File: String = c0("temp")
    val tempBinaryFile: String = out("temp")
  }

  def resolveOutputFiles(
      dir: String,
      disableBaseline: Boolean = false
  ): BenchmarkOutputFiles = {
    new Directory(Paths.get(dir).toFile).deleteRecursively()
    val root = Paths.get(dir)
    Files.createDirectories(root)

    val perms = root.resolve(Names.perms)
    Files.createDirectories(perms)

    val verifiedPerms = root.resolve(Names.verified_perms)
    Files.createDirectories(verifiedPerms)

    val baselinePerms: Option[Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.baselinePerms)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val performance = root.resolve(Names.performance)
    Files.createDirectories(performance)
    val baselinePerformance = root.resolve(Names.baselinePerformance)
    Files.createDirectories(baselinePerformance)

    val levels = root.resolve(Names.levels)
    val metadata = root.resolve(Names.metadata)

    val logs = root.resolve(Names.logs)
    Files.createDirectories(logs)

    val verifyLog = logs.resolve(Names.verifyLogs)
    val compileLog = logs.resolve(Names.compilationLogs)
    val baselineCompileLog = logs.resolve(Names.baselineCompilationLogs)

    val exec = logs.resolve(Names.execLogs)
    val baselineExec = logs.resolve(Names.baselineExecLogs)

    BenchmarkOutputFiles(
      root = root,
      perms = perms,
      verifiedPerms = verifiedPerms,
      baselinePerms = baselinePerms,
      logs = logs,
      verifyLogs = verifyLog,
      compilationLogs = compileLog,
      baselineCompilationLogs = baselineCompileLog,
      execLogs = exec,
      baselineExecLogs = baselineExec,
      performance = performance,
      baselinePerformance = baselinePerformance,
      levels = levels,
      metadata = metadata
    )
  }

  def mark(
      source: String,
      config: Config,
      outputFiles: OutputFileCollection,
      librarySearchDirs: List[String]
  ): Unit = {

    val paths = config.benchmarkPaths.getOrElse(1)
    val pathDesc =
      s"${Output.blue(paths.toString)} path" +
        (if (paths > 1) "s" else "")

    val iterations = config.benchmarkIterations.getOrElse(1)
    val iterDesc =
      if (config.onlyVerify) ""
      else
        s"${Output.blue(iterations.toString)} iteration" +
          (if (iterations > 1) "s" else "") + " per permutation"
    val file = c0(outputFiles.baseName)
    val files =
      resolveOutputFiles(config.compileBenchmark.get, config.disableBaseline)
    val timeout = config.timeout match {
      case Some(value) => value.toString + "s"
      case None        => "infinite"
    }
    Output.info(
      s"Benchmarking $pathDesc with $iterDesc for ${blue(
        file
      )}, timeout ${blue(timeout)}, output to ${blue(files.root.toString)}"
    )

    def booleanToStatus(a: Boolean): String =
      if (a) Output.green("enabled") else Output.red("disabled")

    Output.info(
      s"Baseline ${booleanToStatus(!config.disableBaseline)}, execution ${booleanToStatus(!config.onlyVerify)}"
    )

    markVerification(
      source,
      config,
      outputFiles,
      files,
      librarySearchDirs
    )
    println(s"\n\n${Output.formatSuccess("Verification completed.")}\n")

    if (!config.onlyVerify) {
      markExecution(config, files)
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
      source: String,
      config: Config,
      outputFiles: OutputFileCollection,
      files: BenchmarkOutputFiles,
      librarySearchDirs: List[String]
  ): Unit = {
    val alreadySampled = mutable.Set[String]()
    var previousID: Option[String] = None
    val maxPaths = config.benchmarkPaths.getOrElse(1)

    val ir = Main.generateIR(source, librarySearchDirs)

    val selector = new SelectVisitor(ir)
    val labeller = new LabelVisitor()
    val labels = labeller.visit(ir)
    val csv = new CSVPrinter(files, labels)
    val err = new ErrorCSVPrinter(files.verifyLogs)
    val sampler = new Sampler()
    val progress = new VerificationTracker(labels.length - 1, maxPaths)

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

    val outputBottom =
      files.perms.resolve(c0(Names._bottom))
    val outputBottomText = GraphPrinter.print(ir, includeSpecs = false)
    Main.writeFile(
      outputBottom.toString,
      outputBottomText
    )
    val outputTop = files.perms.resolve(c0(Names._top))
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(ir, includeSpecs = false)
    )

    for (sampleIndex <- 0 until maxPaths) {
      val sampleToPermute = sampler.sample(labels, SamplingHeuristic.Random)
      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()

      for (labelIndex <- 0 to sampleToPermute.length - 2) {

        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val id = csv.createID(currentPermutation)
        csv.logPermutation(id, currentPermutation)

        if (!alreadySampled.contains(id)) {
          val builtPermutation = selector.visit(permutationIndices)
          val sourceText =
            GraphPrinter.print(builtPermutation, includeSpecs = true)
          dumpPermutation(
            files.perms,
            c0(id),
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
                  files.verifiedPerms,
                  c0(id),
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
                    files.baselinePerms.get,
                    c0(id),
                    currentPermutation,
                    baselineSourceText
                  )
                }
              case None =>
            }
          } catch {
            case ex: VerificationException =>
              progress.error()
              err.log(id, 1, ex.message)
            case _: TimeoutException =>
              progress.timeout()
              val message =
                s"\n\n ---[Timeout after ${config.timeout.get} ms]---\n"
              println(message)
              err.log(
                id,
                exitCode = 1,
                message
              )
          }
          alreadySampled += id
          progress.incrementUnique()
        } else {
          progress.increment()
        }
        csv.logStep(id, sampleIndex + 1, labelIndex + 1)
        previousID = Some(id)
      }
    }
    if (!config.disableBaseline) {
      BaselineChecker.check(ir)
      val baselineSourceText = GraphPrinter.print(ir, includeSpecs = false)
      dumpPermutation(
        files.baselinePerms.get,
        c0(Names._baseline),
        mutable.TreeSet[ASTLabel]()(LabelOrdering),
        baselineSourceText
      )
    }
    csv.close()
    err.close()
  }

  case class StressScaling(stepSize: Int, upperBound: Int)

  def markExecution(
      config: Config,
      files: BenchmarkOutputFiles
  ): Unit = {
    val iterations = config.benchmarkIterations.getOrElse(1)

    val scaling: Option[StressScaling] = config.benchmarkStepSize match {
      case Some(value) =>
        Some(StressScaling(value, config.benchmarkMaxFactor.getOrElse(value)))
      case None =>
        config.benchmarkMaxFactor match {
          case Some(value) => Some(StressScaling(1, value))
          case None        => None
        }
    }
    markDirectory(
      files.verifiedPerms,
      files.performance,
      scaling,
      ExecutionType.Gradual
    )

    if (!config.disableBaseline) {
      println("\n")
      markDirectory(
        files.baselinePerms.get,
        files.baselinePerformance,
        scaling,
        ExecutionType.Dynamic
      )
    }

    def markDirectory(
        in: Path,
        out: Path,
        scaling: Option[StressScaling],
        verificationType: ExecutionType
    ): Unit = {
      val printer = new PerformanceCSVPrinter(out)
      val runlist = in.toFile.listFiles()
      val progress = new ExecutionTracker(runlist.length, verificationType)

      runlist.indices.foreach(index => {
        scaling match {
          case Some(value) =>
            markFileScaled(
              index,
              value
            )
          case None =>
            markFile(
              index,
              None
            )
        }
      })

      def markFile(
          index: Int,
          stressLevelOption: Option[Int]
      ): Unit = {
        val file = runlist(index)
        val id = file.getName.replaceFirst("[.][^.]+$", "")
        val tempC0File = Paths.get(Names.tempC0File)
        val tempBinaryFile = Paths.get(Names.tempBinaryFile)

        val errCC0 = new ErrorCSVPrinter(files.compilationLogs)
        val errExec = new ErrorCSVPrinter(files.execLogs)
        val source = Files.readString(file.toPath)
        val found = firstAssign.findAllMatchIn(source)

        val stressLevel = stressLevelOption.getOrElse(10)
        if (found.toList.length != 1) {
          throw new BenchmarkException(
            s"The first statement in a benchmarking program must of the form 'int ${Names.stressDeclaration} = ...', and it can only be declared once."
          )
        } else {
          source.replaceFirst(assign.toString(), s"int stress = $stressLevel;")
        }

        try {
          Main.writeFile(
            tempC0File.toAbsolutePath.toString,
            source
          )
          val perf = CapturedExecution.compile_and_exec(
            tempC0File,
            tempBinaryFile,
            iterations,
            config
          )
          printer.logID(id, stressLevel, perf)
        } catch {
          case co: CapturedOutputException =>
            co match {
              case cc0: CC0CompilationException =>
                cc0.logMessage(id, errCC0)
                progress.cc0Error()
              case exec: ExecutionException =>
                exec.logMessage(id, errExec)
                progress.execError()
            }
        } finally {
          if (Files.exists(tempC0File)) Files.delete(tempC0File)
          if (Files.exists(tempBinaryFile)) Files.delete(tempBinaryFile)
        }
        progress.increment()
        errCC0.close()
        errExec.close()
      }

      def markFileScaled(
          index: Int,
          scaling: StressScaling
      ): Unit = {
        for (i <- 0 to scaling.upperBound by scaling.stepSize) {
          markFile(index, Some(i))
        }
      }
    }
  }
}
