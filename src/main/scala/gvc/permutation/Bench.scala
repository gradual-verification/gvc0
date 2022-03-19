package gvc.permutation

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
      levels: Path,
      metadata: Path
  )

  object Names {
    val _baseline = "baseline.c0"
    val _top = "top.c0"
    val _bottom = "bot.c0"
    val perms = "/perms"
    val verified_perms = "/verified_perms"
    val compiled = "/compiled"
    val baselinePerms = "/baseline_perms"
    val baselineCompiled = "'/baseline_compiled"
    val levels = "/levels.csv"
    val metadata = "/metadata.csv"
  }

  def compile(input: String, output: String, config: Config): Int = {
    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(output),
      includeDirs = List(Paths.get("src/main/resources").toAbsolutePath + "/"),
      compilerArgs = if (config.enableProfiling) List("-lprofiler") else List()
    )
    CC0Wrapper.exec(input, cc0Options)
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
    BenchmarkOutputFiles(
      root,
      perms,
      verifiedPerms,
      compiled,
      baselinePerms,
      baselineCompiled,
      levels,
      metadata
    )
  }

  def mark(
      source: String,
      config: Config,
      outputFiles: OutputFileCollection
  ): Unit = {
    val ir = Main.generateIR(source)
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
    println(s"# of components: ${labels.length}")

    val alreadySampled = mutable.Set[String]()
    val csv = new CSVPrinter(files, labels)
    var previousID: Option[String] = None
    val maxPaths = config.benchmarkPaths.getOrElse(1)

    var verificationFailures = 0
    var defaultCompilationFailures = 0
    var baselineCompilationFailures = 0

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
          val permutationSourceFile =
            files.perms.resolve(
              id + ".c0"
            )
          val builtPermutation = selector.visit(permutationIndices)
          val sourceText =
            GraphPrinter.print(builtPermutation, includeSpecs = true)

          val permutationSourceText =
            LabelTools.appendPathComment(
              sourceText,
              currentPermutation.toList
            )
          Main.writeFile(
            permutationSourceFile.toString,
            permutationSourceText
          )

          val verifiedPermutationSourceFile =
            files.perms.resolve(
              id + ".c0"
            )
          try {
            val verifiedPermutation = verify(sourceText, outputFiles, config)

            val verifiedSourceText = LabelTools.appendPathComment(
              verifiedPermutation.c0Source,
              currentPermutation.toList
            )

            Main.writeFile(
              verifiedPermutationSourceFile.toString,
              verifiedSourceText
            )

            val compileDefault =
              files.compiled.resolve(id + ".out").toString

            val exitCodeDefault: Int =
              compile(permutationSourceFile.toString, compileDefault, config)
            if (exitCodeDefault != 0) defaultCompilationFailures += 1

            if (!config.disableBaseline) {
              val baselinePermutationSourceFile =
                files.baselinePerms.get.resolve(
                  id + ".c0"
                )
              Baseline.insert(builtPermutation)
              val baselinePermutationSourceText = LabelTools.appendPathComment(
                GraphPrinter.print(builtPermutation, includeSpecs = false),
                currentPermutation.toList
              )
              Main.writeFile(
                baselinePermutationSourceFile.toString,
                baselinePermutationSourceText
              )
              val compileBaseline =
                files.baselineCompiled.get.resolve(id + ".out").toString
              val exitCodeBaseline = compile(
                baselinePermutationSourceFile.toString,
                compileBaseline,
                config
              )
              if (exitCodeBaseline != 0) baselineCompilationFailures += 1
            }
          } catch {
            case _: VerificationException => verificationFailures += 1
          }

          csv.logPermutation(id, currentPermutation)
          alreadySampled += id
        }
        csv.logStep(id, sampleIndex + 1, labelIndex + 1)
        print(
          s"\rGenerated ${alreadySampled.size + 3} unique programs, ${sampleIndex + 1}/$maxPaths paths completed. Errors: ($verificationFailures V, $defaultCompilationFailures C, $baselineCompilationFailures CB"
        )
        previousID = Some(id)
      }
    }
    csv.close()
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
