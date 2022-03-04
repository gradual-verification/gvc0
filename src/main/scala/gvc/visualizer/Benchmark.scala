package gvc.visualizer
import gvc.CC0Wrapper.CC0Exception
import gvc.Main.{ProfilingInfo, VerifiedOutput, deleteFile, writeFile}
import gvc.{CC0Options, CC0Wrapper, Config, Main, OutputFileCollection}
import gvc.transformer.GraphPrinter
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic

import java.io.FileWriter
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.reflect.io.Directory

case class SamplingInfo(heuristic: SamplingHeuristic, nSamples: Int)

object Bench {

  class BenchmarkException(message: scala.Predef.String)
      extends Exception(message)

  class VerificationException(message: scala.Predef.String)
      extends BenchmarkException(message)

  class ExecutionException(message: scala.Predef.String)
      extends BenchmarkException(message)

  private object Names {
    val _stats = "stats.csv"
    val _top = "top.c0"
    val _imprecise_bottom = "bot_imp.c0"
    val _precise_bottom = "bot.c0"
    val _temporaryBenchmarkFile = "temp.c0"
    val _compiledOutput = "a.out"
  }

  private def mark(
      sourceText: String,
      timedIterations: Int,
      fileNames: OutputFileCollection,
      config: Config
  ): PerformanceMetrics = {
    val verifierResults =
      markVerifier(sourceText, timedIterations, fileNames, config)
    val executionTime =
      markExecution(verifierResults.output.c0Source, timedIterations, config)
    PerformanceMetrics(
      verifierResults.duration,
      executionTime,
      verifierResults.output.profiling
    )
  }

  private def markVerifier(
      sourceText: String,
      timedIterations: Int,
      fileNames: OutputFileCollection,
      config: Config
  ): TimedVerifiedOutput = {
    var duration: Long = 0
    val verifiedIR = Main.verify(sourceText, fileNames, config)
    for (_ <- 1 to timedIterations) {
      val start = System.nanoTime()
      Main.verify(sourceText, fileNames, config)
      val stop = System.nanoTime()
      duration = (duration + (stop - start)) / 2
    }
    TimedVerifiedOutput(verifiedIR, duration)
  }

  private def markExecution(
      sourceText: String,
      timedIterations: Int,
      config: Config
  ): Long = {
    val outputExe = config.output.getOrElse(Names._compiledOutput)
    val runtimeInput =
      Paths.get(getClass.getResource("/runtime.c0").getPath)
    val runtimeIncludeDir = runtimeInput.getParent.toAbsolutePath

    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = config.saveFiles,
      output = Some(outputExe),
      includeDirs = List(Paths.get(runtimeIncludeDir.toString, "/").toString)
    )

    val c0FileName = Names._temporaryBenchmarkFile
    writeFile(c0FileName, sourceText)
    val executionTime =
      try {
        CC0Wrapper.execTimed(c0FileName, cc0Options, timedIterations)
      } finally {
        deleteFile(c0FileName)
      }
    executionTime
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
      new FileWriter(config.permute.get)
    statsFile.flush()

    var nVerificationFailures = 0
    var nExecutionFailures = 0
    var averageExecutionTime: Long = 0
    var averageVerificationTime: Long = 0
    for (sampleIndex <- 0 until sampling.nSamples) {

      val sampleToPermute = Labeller.sample(labels, sampling.heuristic)

      var permutationHash = ""
      val currentPermutation = mutable.TreeSet()(Labeller.LabelOrdering)

      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        printProgress(
          fileNames.baseName + ".c0",
          sampleIndex + 1,
          sampling.nSamples,
          labelIndex + 1,
          sampleToPermute.length - 1,
          nVerificationFailures,
          nExecutionFailures,
          averageVerificationTime,
          averageExecutionTime
        )
        val permutationSourceFile =
          dest.resolve(
            (sampleIndex + 1) + "_" + (labelIndex + 1) + ".c0"
          )

        currentPermutation += sampleToPermute(labelIndex)
        permutationHash = currentPermutation.foldLeft("")(_ + _.hash)

        val potentiallyExists = lattice.get(permutationHash)
        if (potentiallyExists.isDefined) {

          val csvEntry = lattice.createCSVEntry(
            potentiallyExists.get
          )
          statsFile.write(csvEntry)
          statsFile.flush()
        } else {
          val builtPermutation = PermutationGenerator.generatePermutation(
            currentPermutation.toList,
            program
          )

          val permutationSourceText =
            appendPathComment(
              GraphPrinter.print(builtPermutation, includeSpecs = true),
              currentPermutation.toList
            )

          Main.writeFile(
            permutationSourceFile.toString,
            permutationSourceText
          )

          try {
            val performance = Bench.mark(
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
            case runtime: CC0Exception =>

          }
        }
      }
    }
  }

  def appendPathComment(
      str: String,
      labels: List[Labeller.ASTLabel]
  ): String = {
    "/*\n" +
      labels.foldLeft("")(_ + _.hash + '\n') +
      "*/\n" +
      str
  }

  def printProgress(
      sourceFileName: String,
      currentPath: Int,
      maxPath: Int,
      currentIndex: Int,
      maxIndex: Int,
      nVerFailures: Double,
      nExecFailures: Double,
      averageVerificationTime: Long,
      averageExecutionTime: Long
  ): Unit = {

    def round(x: Double) = {
      val roundBy = 2
      val w = math.pow(10, roundBy)
      (x * w).toLong.toDouble / w
    }
    val baseline = (currentIndex + (currentPath * maxIndex))

    val verFailurePercentage = (nVerFailures) / baseline * 100
    val execFailurePercentage = (nExecFailures) / baseline * 100
    val failurePercentage =
      verFailurePercentage + execFailurePercentage

    var timeRemaining =
      (averageExecutionTime + averageVerificationTime) * (((maxPath - currentPath) * maxIndex) + (maxIndex - currentIndex)) / Math
        .pow(10, 9) / 60
    var postfix = "min."
    if (timeRemaining > 60) {
      timeRemaining = timeRemaining / 60
      postfix = "hr."
    }

    print(
      s"\rBench: ${sourceFileName} * Path ${currentPath}/${maxPath} * Perm. ${currentIndex}/${maxIndex} * Fails: ${round(
        failurePercentage
      )}% - (V: ${round(verFailurePercentage)}% + E: ${round(execFailurePercentage)}%) * Ver. time: ${round(
        averageVerificationTime / Math
          .pow(10, 9)
      )} sec. * Exec time: ${round(
        averageExecutionTime / Math
          .pow(10, 9)
      )} sec. * Time left: ${round(timeRemaining)} ${postfix}"
    )
  }
}

case class TimedVerifiedOutput(
    output: VerifiedOutput,
    duration: Long
)

case class PerformanceMetrics(
    verification: Long,
    execution: Long,
    profiling: ProfilingInfo
)
