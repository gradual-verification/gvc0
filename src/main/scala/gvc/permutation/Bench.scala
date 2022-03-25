package gvc.permutation
import gvc.CC0Wrapper.{CompilationOutput, ExecutionOutput, Performance}
import gvc.Main.verify
import gvc.transformer.GraphPrinter
import gvc.{
  CC0Options,
  CC0Wrapper,
  Config,
  Main,
  OutputFileCollection,
  VerificationException
}

import java.io.{ByteArrayOutputStream, File, FileWriter}
import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.io.Directory
import sys.process._
import scala.language.postfixOps
object Bench {
  val assign = "(int[ ]+stress[ ]*=[ ]*[0-9]+[ ]*;)".r
  val firstAssign =
    "(int[ ]+main[ ]*\\([ ]*\\)\\s*\\{\\s*int[ ]+stress[ ]*=[ ]*[0-9]+[ ]*;)".r
  class BenchmarkException(message: String) extends Exception(message)

  def c0(basename: String): String = basename + ".c0"

  def out(basename: String): String = basename + ".out"

  def csv(basename: String): String = basename + ".csv"

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
    val _baseline = "baseline.c0"
    val _top = "top"
    val _bottom = "bot"
    val perms = "perms"
    val verified_perms = "verified_perms"
    val baselinePerms = "baseline_perms"
    val performance = "performance"
    val baselinePerformance = "baselinePerformance"
    val levels = "levels.csv"
    val metadata = "metadata.csv"
    val verifyLogs = "verify.log"

    val compilationLogs = "cc0.log"
    val baselineCompilationLogs = "cc0_baseline.log"
    val execLogs = "exec.log"
    val baselineExecLogs = "exec_baseline.log"

    val logs = "logs"
    val stressDeclaration = "stress"
    val entry = "main"
    val tempC0File = "temp.c0"
    val tempBinaryFile = "temp.out"
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
    val files =
      resolveOutputFiles(config.compileBenchmark.get, config.disableBaseline)
    markVerification(
      source,
      config,
      outputFiles,
      files,
      librarySearchDirs
    )
    if (!config.onlyVerify)
      markExecution(config, files)
  }

  def markVerification(
      source: String,
      config: Config,
      outputFiles: OutputFileCollection,
      files: BenchmarkOutputFiles,
      librarySearchDirs: List[String]
  ): Unit = {
    var verificationFailures = 0
    val alreadySampled = mutable.Set[String]()
    var previousID: Option[String] = None
    val maxPaths = config.benchmarkPaths.getOrElse(1)

    val ir = Main.generateIR(source, librarySearchDirs)

    val selector = new SelectVisitor(ir)
    val labeller = new LabelVisitor()
    val labels = labeller.visit(ir)
    val csv = new CSVPrinter(files, labels)
    val err = new ErrorPrinter(files.verifyLogs)

    def printProgress(sampleIndex: Int, pathIndex: Int): Unit = {
      val successRate = Math.abs(
        Math.floor(
          (alreadySampled.size - verificationFailures) / alreadySampled.size.toDouble * 10000
        ) / 100
      )
      print(
        s"\rGenerated ${alreadySampled.size} unique programs — $sampleIndex/$maxPaths paths — Current: $pathIndex/${labels.length} — Remaining: ${labels.length - pathIndex} — Success: $successRate% — Failures: $verificationFailures"
      )
    }

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
      val sampleToPermute = LabelTools.sample(labels, SamplingHeuristic.Random)
      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()

      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val id = csv.createID(currentPermutation)

        if (previousID.isDefined && previousID.get == id) {
          println(sampleToPermute(labelIndex).hash)
          throw new Exception("invalid step in permutation")
        }
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
            val verifiedPermutation = verify(sourceText, outputFiles, config)
            dumpPermutation(
              files.verifiedPerms,
              c0(id),
              currentPermutation,
              verifiedPermutation.c0Source
            )
            if (!config.disableBaseline) {
              val baselinePermutation = selector.visit(permutationIndices)
              Baseline.insert(baselinePermutation)
              val baselineSourceText =
                GraphPrinter.print(baselinePermutation, includeSpecs = false)
              dumpPermutation(
                files.baselinePerms.get,
                c0(id),
                currentPermutation,
                baselineSourceText
              )
            }
          } catch {
            case ex: VerificationException =>
              verificationFailures += 1
              err.log(id, 1, ex.message)
          }
          csv.logPermutation(id, currentPermutation)
          alreadySampled += id
        }
        csv.logStep(id, sampleIndex + 1, labelIndex + 1)
        printProgress(sampleIndex, labelIndex)
        previousID = Some(id)
      }
    }
    if (!config.disableBaseline) {
      Baseline.insert(ir)
      val baselineSourceText = GraphPrinter.print(ir, includeSpecs = false)
      dumpPermutation(
        files.baselinePerms.get,
        c0(Names._baseline),
        mutable.TreeSet[ASTLabel]()(LabelOrdering),
        baselineSourceText
      )
    }
    printProgress(maxPaths, labels.length)
    csv.close()
    err.close()
  }

  def markExecution(
      config: Config,
      files: BenchmarkOutputFiles
  ): Unit = {
    val iterations = config.benchmarkIterations.getOrElse(1)
    val stepSize = config.benchmarkStepSize.getOrElse(10)
    val upperBound = config.benchmarkMaxFactor.getOrElse(stepSize)

    var compilationErrors = 0
    var executionErrors = 0
    markDirectory(files.verifiedPerms, files.performance)
    if (!config.disableBaseline) {
      markDirectory(files.baselinePerms.get, files.baselinePerformance)
    }

    def markDirectory(in: Path, out: Path): Unit = {
      val printer = new PerformancePrinter(out)
      val runlist = in.toFile.listFiles()
      runlist.indices.foreach(index => {
        markFile(
          printer,
          runlist(index),
          runlist(index).getName.replaceFirst("[.][^.]+$", ""),
          index,
          config
        )
      })

      def printProgress(
          sampleIndex: Int,
          stressLevel: Int
      ): Unit = {
        val successRate = Math.abs(
          Math.floor(
            (runlist.size - compilationErrors - executionErrors) / runlist.size.toDouble * 10000
          ) / 100
        )
        print(
          s"""\rBenchmarking ${sampleIndex + 1}/${runlist.length} — Stress Level $stressLevel/$upperBound — Success: $successRate% — Compilation Errors: $compilationErrors — Execution Errors: $executionErrors"""
        )
      }

      def markFile(
          printer: PerformancePrinter,
          file: File,
          id: String,
          index: Int,
          config: Config
      ): Unit = {

        val tempC0File = Paths.get(Names.tempC0File)
        val tempBinaryFile = Paths.get(Names.tempBinaryFile)

        val errCC0 = new ErrorPrinter(files.compilationLogs)
        val errExec = new ErrorPrinter(files.execLogs)

        val source = Files.readString(file.toPath)
        val found = firstAssign.findAllMatchIn(source)
        if (found.toList.size == 1) {
          try {
            for (i <- 0 to upperBound by stepSize) {
              printProgress(index, i)
              val modifiedSource =
                source.replaceAll(assign.toString(), s"int stress = $i;")
              Main.writeFile(
                tempC0File.toAbsolutePath.toString,
                modifiedSource
              )
              val output = compile(
                tempC0File,
                tempBinaryFile,
                config
              )
              if (output.exitCode != 0) {
                throw new CC0CompilationException(output)
              } else {
                val exec = exec_timed(tempBinaryFile, iterations)
                exec.perf match {
                  case Some(value) => printer.logPerformance(id, i, value)
                  case None        => throw new ExecutionException(exec)
                }
              }
            }
          } catch {
            case co: CapturedOutputException =>
              co match {
                case cc0: CC0CompilationException =>
                  cc0.logMessage(id, errCC0)
                  compilationErrors += 1
                case exec: ExecutionException =>
                  exec.logMessage(id, errExec)
                  executionErrors += 1
              }
          } finally {
            if (Files.exists(tempC0File)) Files.delete(tempC0File)
            if (Files.exists(tempBinaryFile)) Files.delete(tempBinaryFile)
          }

        } else {
          throw new BenchmarkException(
            s"The first statement in a benchmarking program must of the form 'int ${Names.stressDeclaration} = ...', and it can only be declared once."
          )
        }
      }
    }

    def compile(
        input: Path,
        output: Path,
        config: Config
    ): CompilationOutput = {
      val cc0Options = CC0Options(
        compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
        saveIntermediateFiles = config.saveFiles,
        output = Some(output.toString),
        includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/")
      )
      CC0Wrapper.exec_output(input.toString, cc0Options)
    }
  }
  def exec_timed(
      binary: Path,
      iterations: Int
  ): ExecutionOutput = {
    val command = binary.toAbsolutePath.toString + " 2>&1"
    val timings = mutable.ListBuffer[Long]()
    val os = new ByteArrayOutputStream()
    var exitCode = 0
    for (_ <- 0 until iterations) {
      val start = System.nanoTime()
      exitCode = (command #> os) !

      val end = System.nanoTime()
      timings += end - start
      if (exitCode != 0) {
        return ExecutionOutput(
          exitCode,
          os.toString("UTF-8"),
          None
        )
      } else {
        os.reset()
      }
    }
    val mean = timings.sum / timings.length
    val max = timings.max
    val min = timings.min
    val stdev =
      if (timings.length > 1)
        Math.sqrt(
          timings.map(_ - mean).map(m => m * m).sum / (timings.length - 1)
        )
      else 0
    ExecutionOutput(
      exitCode,
      os.toString("UTF-8"),
      Some(new Performance(mean, stdev, min, max))
    )
  }

  class ErrorPrinter(file: Path) {
    val writer = new FileWriter(file.toString)
    def formatSection(name: String, exitCode: Int): String =
      s"-----[ Error in $name, Exit: $exitCode ]-----\n"
    def log(name: String, exitCode: Int, err: String): Unit = {
      writer.write(formatSection(name, exitCode) + err + "\n")
      writer.flush()
    }
    def close(): Unit = writer.close()
  }

  class PerformancePrinter(out: Path) {
    var currentWriter: Option[(String, FileWriter)] = None
    val performanceColumnNames: String =
      List("stress", "mean", "stdev", "min", "max").foldRight("")(
        _ + "," + _
      ) + '\n'
    private def replaceWriter(id: String): FileWriter = {
      val contents =
        (id, new FileWriter(out.resolve(csv(id)).toString))
      currentWriter = Some(contents)
      contents._2.write(performanceColumnNames)
      contents._2.flush()
      contents._2
    }
    def logPerformance(
        id: String,
        stress: Int,
        perf: Performance
    ): Unit = {
      val writer: FileWriter = currentWriter match {
        case Some(value) =>
          if (value._1.equals(id)) {
            value._2
          } else {
            value._2.close()
            replaceWriter(id)
          }
        case None => replaceWriter(id)

      }
      writer.write(perf.toString(stress) + '\n')
      writer.flush()
    }
  }
  class CSVPrinter(files: BenchmarkOutputFiles, template: List[ASTLabel]) {
    val metaWriter = new FileWriter(files.metadata.toString)
    val mappingWriter = new FileWriter(files.levels.toString)

    val metadataColumnNames: String =
      (List("id") ++ template.map(_.hash)).foldRight("")(_ + "," + _) + '\n'
    metaWriter.write(metadataColumnNames)

    val mappingColumnNames: String =
      List("id", "path_id", "level_id").foldRight("")(_ + "," + _) + '\n'
    mappingWriter.write(mappingColumnNames)

    def close(): Unit = {
      metaWriter.close()
      mappingWriter.close()
    }

    def createID(permutation: mutable.TreeSet[ASTLabel]): String = {
      new BigInteger(
        template
          .map(label => {
            (if (permutation.contains(label)) 1 else 0).toString
          })
          .foldRight("")(_ + _),
        2
      ).toString(16)
    }

    def logPermutation(
        id: String,
        permutation: mutable.TreeSet[ASTLabel]
    ): String = {
      val entry = ListBuffer[String](id)
      template.foreach(label => {
        val toAppend = (if (permutation.contains(label)) 1 else 0).toString
        entry += toAppend
      })
      metaWriter.write(entry.foldRight("")(_ + "," + _) + '\n')
      metaWriter.flush()
      id
    }

    def logStep(id: String, pathIndex: Int, levelIndex: Int): Unit = {
      mappingWriter.write(
        List(id, pathIndex, levelIndex).foldRight("")(_ + "," + _) + '\n'
      )
      mappingWriter.flush()
    }
  }

  class CapturedOutputException(exitCode: Int, stdout: String)
      extends Exception {
    def logMessage(name: String, printer: ErrorPrinter): Unit = {
      printer.log(name, exitCode, stdout)
    }
  }
  class CC0CompilationException(output: CompilationOutput)
      extends CapturedOutputException(output.exitCode, output.output)
  class ExecutionException(output: ExecutionOutput)
      extends CapturedOutputException(output.exitCode, output.output)
}
