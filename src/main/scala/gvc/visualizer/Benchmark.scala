package gvc.visualizer
import gvc.Main.{deleteFile, writeFile}
import gvc.{CC0Options, CC0Wrapper, Config, Main, OutputFileCollection}
import gvc.transformer.GraphPrinter
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic
import viper.silver.ast.Program

import java.io.FileWriter
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.reflect.io.Directory

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

object Bench {
  private object Names {
    val _stats = "stats.csv"
    val _top = "top.c0"
    val _imprecise_bottom = "bot_imp.c0"
    val _precise_bottom = "bot.c0"
  }

  val columnHeaders =
    "filename,lattice_height,verifier_time_ns,execution_time_ns\n"

  private def mark(
      sourceText: String,
      timedIterations: Int,
      fileNames: OutputFileCollection,
      config: Config
  ): PerformanceMetrics = {
    val verifierOutput =
      markVerifier(sourceText, timedIterations, fileNames)
    val outputExe = config.output.getOrElse("a.out")
    val runtimeInput =
      Paths.get(getClass.getResource("/runtime.c0").getPath)
    val runtimeIncludeDir = runtimeInput.getParent.toAbsolutePath

    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(outputExe),
      includeDirs = List(runtimeIncludeDir.toString + "/")
    )
    val c0FileName = "temp.c0"
    writeFile(c0FileName, verifierOutput.output.c0Source)
    val executionTime =
      try {
        CC0Wrapper.execTimed(c0FileName, cc0Options, timedIterations)
      } finally {
        deleteFile(c0FileName)
      }
    PerformanceMetrics(verifierOutput.duration, executionTime)
  }

  private def markVerifier(
      sourceText: String,
      timedIterations: Int,
      fileNames: OutputFileCollection
  ): TimedVerifiedOutput = {
    var duration: Long = 0
    val verifiedIR = Main.verify(sourceText, fileNames)
    for (_ <- 1 to timedIterations) {
      val start = System.nanoTime()
      Main.verify(sourceText, fileNames)
      val stop = System.nanoTime()
      duration = (duration + (stop - start)) / 2
    }
    TimedVerifiedOutput(verifiedIR, duration)
  }

  def run(
      inputSource: String,
      sampling: SamplingInfo,
      fileNames: OutputFileCollection,
      config: Config
  ): Unit = {
    val program = Main.generateIR(inputSource)
    val outputDir = config.permuteDumpDir.getOrElse("./perms")

    val dest = Paths.get(outputDir)
    new Directory(dest.toFile).deleteRecursively()

    Files.createDirectories(dest)
    val outputBottomPrecise = dest.resolve(Names._precise_bottom)
    Main.writeFile(
      outputBottomPrecise.toString,
      GraphPrinter.print(program, includeSpecs = false)
    )

    val outputBottomImprecise = dest.resolve(Names._imprecise_bottom)
    Main.writeFile(
      outputBottomImprecise.toString,
      GraphPrinter.print(
        PermutationGenerator.generatePermutation(List.empty, program),
        includeSpecs = true
      )
    )

    val outputTop = dest.resolve(Names._top)
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(program, includeSpecs = true)
    )

    val labels = Labeller.labelAST(program)
    val lattice = new Lattice()
    val statsFile =
      new FileWriter(dest.resolve(Names._stats).toString)

    statsFile.write(columnHeaders)
    statsFile.flush()

    for (sampleIndex <- 0 until sampling.nSamples) {
      val directory = dest.resolve(sampleIndex.toString)
      Files.createDirectories(directory)

      val sampleToPermute = Labeller.sample(labels, sampling.heuristic)

      var permutationHash = ""
      val currentPermutation = mutable.ListBuffer[ASTLabel]()

      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        val permutationSourceFile =
          directory.resolve(
            (sampleIndex + 1) + "_" + (labelIndex + 1) + ".c0"
          )

        currentPermutation += sampleToPermute(labelIndex)
        permutationHash += sampleToPermute(labelIndex).hash

        val potentiallyExists = lattice.get(permutationHash)
        if (potentiallyExists.isDefined) {

          val csvEntry = lattice.createCSVEntry(
            potentiallyExists.get,
            permutationSourceFile.toString
          )
          statsFile.write(csvEntry)
          statsFile.flush()
        } else {
          val builtPermutation = PermutationGenerator.generatePermutation(
            currentPermutation.toList,
            program
          )

          val permutationSourceText =
            GraphPrinter.print(builtPermutation, includeSpecs = true)

          Main.writeFile(
            permutationSourceFile.toString,
            permutationSourceText
          )

          try {
            println(
              "Benchmarking '" + permutationSourceFile.toString + "'...\n"
            )
            val performance: PerformanceMetrics = Bench.mark(
              permutationSourceText,
              timedIterations = 1,
              fileNames,
              config
            )
            val csvEntry = lattice.createCSVEntry(
              lattice.add(
                performance,
                currentPermutation.toList,
                permutationSourceFile
              ),
              permutationSourceFile.toString
            )
            statsFile.write(csvEntry)
            statsFile.flush()

          } catch {
            case e: Throwable =>
              print("\n------------\n")
              println(
                "Exception while running benchmark `" + permutationSourceFile.toString + "`:"
              )
              e.printStackTrace()
              print("\n------------\n")
          }
        }
      }
    }
  }
}

case class VerifiedOutput(silver: Program, c0Source: String)
case class TimedVerifiedOutput(
    output: VerifiedOutput,
    duration: Long
)

case class PerformanceMetrics(verification: Long, execution: Long)

case class LatticeElement(
    metrics: PerformanceMetrics,
    specsPresent: List[ASTLabel],
    originallyWrittenTo: Path
)

class Lattice {
  val levels: mutable.ListBuffer[mutable.ListBuffer[LatticeElement]] =
    mutable.ListBuffer[mutable.ListBuffer[LatticeElement]]()
  val elementMap: mutable.Map[String, LatticeElement] =
    mutable.Map[String, LatticeElement]()

  def get(hash: String): Option[LatticeElement] = {
    elementMap.get(hash)
  }
  def add(
      metrics: PerformanceMetrics,
      specsPresent: List[ASTLabel],
      originallyWrittenTo: Path
  ): LatticeElement = {
    val toAppend = LatticeElement(
      metrics,
      specsPresent,
      originallyWrittenTo
    )
    elementMap += specsPresent.foldLeft("")(_ + _.hash) -> toAppend
    toAppend
  }
  def createCSVEntry(
      latticeElement: LatticeElement,
      sourceFileName: String
  ): String = {
    val entry = mutable.ListBuffer[String]()
    entry += sourceFileName
    entry += latticeElement.specsPresent.length.toString
    entry += latticeElement.metrics.execution.toString
    entry += latticeElement.metrics.verification.toString
    entry.foldLeft("")(_ + "," + _) + "\n"
  }
}
