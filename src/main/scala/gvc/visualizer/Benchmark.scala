package gvc.visualizer
import gvc.Main.{deleteFile, writeFile}
import gvc.{CC0Options, CC0Wrapper, Config, Main, OutputFileCollection}
import gvc.transformer.GraphPrinter
import gvc.visualizer.Labeller.ASTLabel
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic
import viper.silver.ast.Program
import scala.language.postfixOps

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
  }
  val columnHeaders =
    "path_id,lattice_height,verifier_time_ns,execution_time_ns,total_conjuncts,eliminated_conjuncts,src\n"

  private def mark(
      sourceText: String,
      timedIterations: Int,
      fileNames: OutputFileCollection,
      config: Config
  ): PerformanceMetrics = {
    val verifierOutput =
      markVerifier(sourceText, timedIterations, fileNames)

    if (verifierOutput.output.isDefined) {

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
      writeFile(c0FileName, verifierOutput.output.get.c0Source)
      val executionTime =
        try {
          CC0Wrapper.execTimed(c0FileName, cc0Options, timedIterations)
        } catch {
          case _: Throwable => {
            throw new ExecutionException("Execution failed.")
          }
        } finally {
          deleteFile(c0FileName)
        }
      PerformanceMetrics(
        verifierOutput.duration,
        executionTime,
        verifierOutput.output.get.totalConjuncts,
        verifierOutput.output.get.eliminatedConjuncts
      )

    } else {
      throw new VerificationException("Verification failed.")
    }
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
      new FileWriter(config.permute.get)

    statsFile.write(columnHeaders)
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

            if (averageExecutionTime > 0)
              averageExecutionTime =
                (averageExecutionTime + performance.execution) / 2
            else averageExecutionTime = performance.execution

            if (averageVerificationTime > 0)
              averageVerificationTime =
                (averageVerificationTime + performance.verification) / 2
            else averageVerificationTime = performance.verification

            val csvEntry = lattice.createCSVEntry(
              lattice.add(
                performance,
                currentPermutation.toList,
                sampleIndex + 1,
                permutationSourceFile
              )
            )
            statsFile.write(csvEntry)
            statsFile.flush()

          } catch {
            case _: VerificationException =>
              nVerificationFailures += 1
            case _: ExecutionException =>
              nExecutionFailures += 1
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

case class VerifiedOutput(
    silver: Program,
    c0Source: String,
    totalConjuncts: Int,
    eliminatedConjuncts: Int
)
case class TimedVerifiedOutput(
    output: Option[VerifiedOutput],
    duration: Long
)

case class PerformanceMetrics(
    verification: Long,
    execution: Long,
    nConjuncts: Int,
    nConjunctsEliminated: Int
)

case class LatticeElement(
    pathIndex: Int,
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
      pathIndex: Int,
      originallyWrittenTo: Path
  ): LatticeElement = {
    val toAppend = LatticeElement(
      pathIndex,
      metrics,
      specsPresent,
      originallyWrittenTo
    )
    elementMap += specsPresent.foldLeft("")(_ + _.hash) -> toAppend
    toAppend
  }
  def createCSVEntry(
      latticeElement: LatticeElement
  ): String = {
    val entry = mutable.ListBuffer[String]()
    entry += latticeElement.pathIndex.toString
    entry += latticeElement.specsPresent.length.toString
    entry += latticeElement.metrics.execution.toString
    entry += latticeElement.metrics.verification.toString
    entry += latticeElement.metrics.nConjuncts.toString
    entry += latticeElement.metrics.nConjunctsEliminated.toString
    entry += latticeElement.originallyWrittenTo.toString
    entry.foldRight("")(_ + "," + _) + "\n"
  }

}
