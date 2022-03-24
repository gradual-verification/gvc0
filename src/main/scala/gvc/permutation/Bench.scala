package gvc.permutation
import gvc.CC0Wrapper.{CompilationOutput, ExecutionOutput, Performance}
import gvc.Main.{generateIR, verify}
import gvc.transformer.IRGraph.Method
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.{
  CC0Options,
  CC0Wrapper,
  Config,
  Main,
  OutputFileCollection,
  VerificationException
}
import java.io.{ByteArrayOutputStream, FileWriter}
import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.io.Directory
import sys.process._
import scala.language.postfixOps
object Bench {

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

    val profilerLinkingFlag = "-lprofiler"
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
      markExecution(config, files, librarySearchDirs)
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

    def printProgress(sampleIndex: Int): Unit = {
      val successRate = Math.abs(
        Math.floor(
          (alreadySampled.size - verificationFailures) / alreadySampled.size.toDouble * 10000
        ) / 100
      )
      print(
        s"\rGenerated ${alreadySampled.size} unique programs, $sampleIndex/$maxPaths paths (${labels.length} perms/path) completed. Success: $successRate%, Failures: $verificationFailures)"
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
              err.log(id, ex.message)
          }
          csv.logPermutation(id, currentPermutation)
          alreadySampled += id
        }
        csv.logStep(id, sampleIndex + 1, labelIndex + 1)
        printProgress(sampleIndex)
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
    printProgress(maxPaths)
    csv.close()
    err.close()
  }

  def markExecution(
      config: Config,
      files: BenchmarkOutputFiles,
      librarySearchDirs: List[String]
  ): Unit = {
    var compilationErrors = 0
    var executionErrors = 0

    def markDirectory(in: Path, out: Path): Unit = {
      val printer = new PerformancePrinter(out)
      in.toFile
        .listFiles()
        .foreach(file => {
          val source = Files.readString(file.toPath)
          val ast = generateIR(source, librarySearchDirs)
          markFile(
            printer,
            ast,
            file.getName.replaceFirst("[.][^.]+$", ""),
            config
          )
        })
    }

    def markFile(
        printer: PerformancePrinter,
        ir: IRGraph.Program,
        id: String,
        config: Config
    ): List[CompilationOutput] = {
      val tempC0File = Paths.get(Names.tempC0File)
      val tempBinaryFile = Paths.get(Names.tempBinaryFile)
      val errCC0 = new ErrorPrinter(files.compilationLogs)
      val errExec = new ErrorPrinter(files.execLogs)

      val firstOperationOption =
        ir.method(Names.entry).asInstanceOf[Method].body.headOption
      val assignment = firstOperationOption match {
        case Some(value) =>
          value match {
            case assign: IRGraph.Assign
                if assign.target.name.equals(
                  Names.stressDeclaration
                ) && assign.target.varType.equals(IRGraph.IntType) =>
              assign
            case _ =>
              throw new BenchmarkException(
                s"The first statement in a benchmarking program must of the form 'int ${Names.stressDeclaration} = ...'"
              )
          }
        case None =>
          throw new BenchmarkException(
            s"The body of '${Names.entry}' is empty."
          )
      }
      val step = config.benchmarkStepSize.getOrElse(100)
      val upper = config.benchmarkMaxFactor.getOrElse(1000)
      if (upper < step || upper % step != 0) {
        throw new BenchmarkException(
          "The upper bound on the stress factor must be evenly divided by the step size."
        )
      } else {
        val outputBuffer = mutable.ListBuffer[CompilationOutput]()
        for (i <- 0 until upper by step) {
          assignment.value = new IRGraph.Int(i)
          val source = GraphPrinter.print(ir, includeSpecs = false)
          Main.writeFile(tempC0File.toAbsolutePath.toString, source)
          val output = compile(
            tempC0File,
            tempBinaryFile,
            config
          )
          if (output.exitCode != 0) {
            errCC0.log(id, output.output)
            compilationErrors += 1
          } else {
            val exec = exec_timed(tempBinaryFile, config)
            exec.perf match {
              case Some(value) => printer.logPerformance(id, i, value)
              case None =>
                errExec.log(id, exec.output)
                executionErrors += 1
            }
          }
        }

        if (Files.exists(tempC0File)) Files.delete(tempC0File)
        if (Files.exists(tempBinaryFile)) Files.delete(tempBinaryFile)

        outputBuffer.toList
      }
    }

    markDirectory(files.perms, files.performance)
    if (!config.disableBaseline) {
      markDirectory(files.baselinePerms.get, files.baselinePerformance)
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
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/"),
      compilerArgs =
        if (config.enableProfiling) List(Names.profilerLinkingFlag)
        else List()
    )
    CC0Wrapper.exec_output(input.toString, cc0Options)
  }

  def exec_timed(binary: Path, config: Config): ExecutionOutput = {
    val command = binary.toAbsolutePath.toString
    val timings = mutable.ListBuffer[Long]()
    val os = new ByteArrayOutputStream()
    var exitCode = 0
    for (_ <- 0 until config.benchmarkIterations.get) {
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
      Math.sqrt(
        timings.map(_ - mean).map(m => m * m).sum / (timings.length - 1)
      )
    ExecutionOutput(
      exitCode,
      os.toString("UTF-8"),
      Some(new Performance(mean, stdev, min, max))
    )
  }

  class ErrorPrinter(file: Path) {
    val writer = new FileWriter(file.toString)
    def formatSection(name: String): String = s"-----[ Error in $name ]-----\n"
    def log(name: String, err: String): Unit = {
      writer.write(formatSection(name) + err + "\n")
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
}
