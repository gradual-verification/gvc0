package gvc.permutation

import gvc.CC0Wrapper.Performance
import gvc.permutation.CapturedExecution.{
  CC0CompilationException,
  ExecutionException,
  compile_and_exec
}
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.{Config, Main, OutputFileCollection}

import java.io.FileWriter
import java.nio.file.{FileSystems, Files, Path, Paths}

object Stress {

  class StressException(message: String) extends Exception(message)

  case class StressTestOutputFiles(
      root: Path,
      all: Path,
      none: Path
  )

  object Names {
    val allEnding = "_all.csv"
    val noneEnding = "_none.csv"
    val stress = "stress"
    val tempExec = "a.out"
    val tempC0 = "temp.c0"
  }

  def resolveOutputFiles(
      config: Config,
      files: OutputFileCollection
  ): StressTestOutputFiles = {
    val root = Paths.get(config.compileStressTest.get)
    Files.createDirectories(root)
    val base = files.baseName.slice(
      files.baseName.lastIndexOf(FileSystems.getDefault.getSeparator) + 1,
      files.baseName.length()
    )
    val all = root.resolve(base + Names.allEnding)
    val none = root.resolve(base + Names.noneEnding)

    StressTestOutputFiles(root, all, none)
  }

  def test(
      source: String,
      config: Config,
      outputFiles: OutputFileCollection,
      librarySearchDirs: List[String]
  ): Unit = {
    val output = resolveOutputFiles(config, outputFiles)
    val ir = Main.generateIR(source, librarySearchDirs)
    val assignmentHook = resolveAssignment(ir)

    assignmentHook match {
      case Some(assign) =>
        config.benchmarkStressMode match {
          case Some(value) =>
            value match {
              case ExecutionType.FullDynamic => BaselineChecker.check(ir)
              case ExecutionType.FramingOnly => BaselineChecker.checkFraming(ir)
              case ExecutionType.Unverified  =>
              case _                         => throw new StressException("Invalid execution type.")
            }
            testExecution(
              ir,
              config,
              output.all,
              assign,
              value
            )
          case None => {
            testExecution(
              ir,
              config,
              output.none,
              assign,
              ExecutionType.Unverified
            )
            BaselineChecker.check(ir)
            testExecution(
              ir,
              config,
              output.all,
              assign,
              ExecutionType.FullDynamic
            )
            val framingIR = Main.generateIR(source, librarySearchDirs)
            val framingAssignmentHook = resolveAssignment(framingIR).get
            testExecution(
              framingIR,
              config,
              output.all,
              framingAssignmentHook,
              ExecutionType.FramingOnly
            )
          }
        }
      case None =>
        throw new StressException(
          "To perform a stress test on a c0 file, the first statement in main must be an assignment of the form 'int stress = ...'"
        )
    }
  }

  def testExecution(
      ir: IRGraph.Program,
      config: Config,
      csvOutput: Path,
      assign: IRGraph.Assign,
      executionType: ExecutionType
  ): Unit = {
    val tempC0 = Paths.get(Names.tempC0)
    val tempExec = Paths.get(Names.tempExec)

    val entries = CSVIO.readEntries(csvOutput, Columns.performanceColumnNames)
    val validEntries =
      entries.filter(_.head.matches("[0-9]+"))
    CSVIO.writeEntries(csvOutput, validEntries, Columns.performanceColumnNames)

    val performanceOutput = new FileWriter(csvOutput.toFile, true)

    val stressSet = validEntries.map(_.head.toInt)

    val upper = config.benchmarkWUpper.getOrElse(1000)
    val step = config.benchmarkWStep.getOrElse(10)
    val iter = config.benchmarkIterations.getOrElse(1)

    val progress = new ExecutionTracker(upper / step + 1, executionType)

    for (i <- 0 to upper by step) {
      if (!stressSet.contains(i)) {
        assign.value = new IRGraph.Int(i)
        val printedSource = GraphPrinter.print(ir, includeSpecs = false)
        Files.writeString(tempC0, printedSource)
        try {
          val perf = compile_and_exec(
            tempC0,
            tempExec,
            config.benchmarkIterations.getOrElse(1),
            List(),
            config
          )
          logPerformance(performanceOutput, i, iter, perf)
        } catch {
          case _: CC0CompilationException => progress.cc0Error()
          case _: ExecutionException      => progress.execError()
        }
      }
      progress.increment()
    }
    performanceOutput.close()
  }

  def resolveAssignment(ir: IRGraph.Program): Option[IRGraph.Assign] = {
    ir.methodBody("main") match {
      case Some(value) =>
        value.headOption match {
          case Some(op) =>
            op match {
              case assign: IRGraph.Assign
                  if (assign.target.name == Names.stress
                    && assign.target.varType == IRGraph.IntType) =>
                Some(assign)
              case _ => None
            }
          case None => None
        }
      case None => None
    }
  }

  def logPerformance(
      writer: FileWriter,
      stress: Int,
      iterations: Int,
      performance: Performance
  ): Unit = {
    val entry = stress + "," + iterations + ',' + performance.toString() + '\n'
    writer.write(entry)
    writer.flush()
  }
}
