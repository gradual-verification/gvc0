package gvc.permutation
import gvc.CC0Wrapper.CompilationOutput
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

import java.io.FileWriter
import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.io.Directory

object Bench {

  class BenchmarkException(message: String) extends Exception(message)

  case class BenchmarkOutputFiles(
      root: Path,
      perms: Path,
      verifiedPerms: Path,
      compiled: Path,
      baselinePerms: Option[Path],
      baselineCompiled: Option[Path],
      logs: Path,
      verifyLogs: Path,
      baselineCompilationLogs: Path,
      compilationLogs: Path,
      levels: Path,
      metadata: Path
  )

  object Names {
    val _baseline = "baseline.c0"
    val _top = "top.c0"
    val _bottom = "bot.c0"
    val perms = "perms"
    val verified_perms = "verified_perms"
    val compiled = "compiled"
    val baselinePerms = "baseline_perms"
    val baselineCompiled = "baseline_compiled"
    val levels = "levels.csv"
    val metadata = "metadata.csv"
    val verifyLogs = "verify.log"
    val compilationLogs = "cc0.log"
    val baselineCompilationLogs = "cc0_baseline.log"
    val profilerLinkingFlag = "-lprofiler"
    val logs = "logs"
  }

  def compile(
      input: String,
      output: String,
      config: Config
  ): CompilationOutput = {
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(output),
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/"),
      compilerArgs =
        if (config.enableProfiling) List(Names.profilerLinkingFlag) else List()
    )
    CC0Wrapper.exec_output(input, cc0Options)
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

    val compiled = root.resolve(Names.compiled)
    Files.createDirectories(compiled)

    val baselineCompiled: Option[Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.baselineCompiled)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val levels = root.resolve(Names.levels)
    val metadata = root.resolve(Names.metadata)

    val logs = root.resolve(Names.logs)
    Files.createDirectories(logs)

    val verifyLog = logs.resolve(Names.verifyLogs)
    val compileLog = logs.resolve(Names.compilationLogs)
    val baselineCompileLog = logs.resolve(Names.baselineCompilationLogs)

    BenchmarkOutputFiles(
      root = root,
      perms = perms,
      verifiedPerms = verifiedPerms,
      compiled = compiled,
      baselinePerms = baselinePerms,
      baselineCompiled = baselineCompiled,
      logs = logs,
      verifyLogs = verifyLog,
      compilationLogs = compileLog,
      baselineCompilationLogs = baselineCompileLog,
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
    val ir = Main.generateIR(source, librarySearchDirs)
    val files =
      resolveOutputFiles(config.compileBenchmark.get, config.disableBaseline)
    val selector = new SelectVisitor(ir)

    val outputBottom =
      files.perms.resolve(Names._bottom)
    Main.writeFile(
      outputBottom.toString,
      GraphPrinter.print(
        selector.visit(mutable.TreeSet.empty[Int]),
        includeSpecs = true
      )
    )

    val outputTop = files.perms.resolve(Names._top)
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(ir, includeSpecs = true)
    )

    val labeller = new LabelVisitor()
    val labels = labeller.visit(ir)

    val alreadySampled = mutable.Set[String]()
    val csv = new CSVPrinter(files, labels)
    val err = new ErrorPrinter(files)
    var previousID: Option[String] = None
    val maxPaths = config.benchmarkPaths.getOrElse(1)

    var verificationFailures = 0
    var defaultCompilationFailures = 0
    var baselineCompilationFailures = 0

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

    def compilePermutation(
        dir: Path,
        name: String,
        inputPath: Path,
        config: Config
    ): CompilationOutput = {
      val compileDefault =
        dir.resolve(name).toString
      compile(inputPath.toString, compileDefault, config)
    }

    def printProgress(sampleIndex: Int) = {
      val allErrors =
        verificationFailures + baselineCompilationFailures + defaultCompilationFailures
      val successRate = Math.floor(
        (alreadySampled.size - allErrors) / alreadySampled.size.toDouble * 10000
      ) / 100
      print(
        s"\rGenerated ${alreadySampled.size} unique programs, ${sampleIndex}/$maxPaths paths (${labels.length} perms/path) completed. Success: ${successRate}%, Failures: ($verificationFailures verification, ${defaultCompilationFailures + baselineCompilationFailures} cc0)"
      )
    }

    def c0(basename: String): String = basename + ".c0"
    def out(basename: String): String = basename + ".out"

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
            val verifiedPath = dumpPermutation(
              files.verifiedPerms,
              c0(id),
              currentPermutation,
              verifiedPermutation.c0Source
            )
            val defaultExit =
              compilePermutation(files.compiled, out(id), verifiedPath, config)

            if (defaultExit.exitCode != 0) {
              defaultCompilationFailures += 1
              err.logCompilationError(id, defaultExit.output)
            }

            if (!config.disableBaseline) {
              val baselinePermutation = selector.visit(permutationIndices)
              Baseline.insert(baselinePermutation)
              val baselineSourceText =
                GraphPrinter.print(baselinePermutation, includeSpecs = false)
              val baselinePath = dumpPermutation(
                files.baselinePerms.get,
                c0(id),
                currentPermutation,
                baselineSourceText
              )
              val baselineExit = compilePermutation(
                files.baselineCompiled.get,
                out(id),
                baselinePath,
                config
              )
              if (baselineExit.exitCode != 0) {
                baselineCompilationFailures += 1
                err.logBaselineCompilationError(id, baselineExit.output)
              }
            }
          } catch {
            case ex: VerificationException =>
              verificationFailures += 1
              err.logVerificationError(id, ex.message)
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
      val baselinePath = dumpPermutation(
        files.baselinePerms.get,
        c0(Names._baseline),
        mutable.TreeSet[ASTLabel]()(LabelOrdering),
        baselineSourceText
      )
      val exit = compilePermutation(
        files.baselineCompiled.get,
        out(Names._baseline),
        baselinePath,
        config
      )
      if (exit.exitCode != 0) {
        baselineCompilationFailures += 1
        err.logBaselineCompilationError(Names._baseline, exit.output)
      }
    }
    printProgress(maxPaths)
    csv.close()
    err.close()
  }

  class ErrorPrinter(files: BenchmarkOutputFiles) {
    val verifyWriter = new FileWriter(files.verifyLogs.toString)
    val compileWriter = new FileWriter(files.compilationLogs.toString)
    val compileBaselineWriter = new FileWriter(
      files.baselineCompilationLogs.toString
    )

    def formatSection(name: String): String =
      s"-----[ Error in ${name} ]-----\n"

    def logVerificationError(name: String, err: String): Unit = {
      verifyWriter.write(formatSection(name) + err + "\n")
      verifyWriter.flush()
    }

    def logCompilationError(name: String, err: String): Unit = {
      compileWriter.write(formatSection(name) + err + '\n')
      compileWriter.flush()
    }
    def logBaselineCompilationError(name: String, err: String): Unit = {
      compileBaselineWriter.write(formatSection(name) + err + '\n')
      compileBaselineWriter.flush()
    }
    def close(): Unit = {
      verifyWriter.close()
      compileWriter.close()
      compileBaselineWriter.close()
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
