package gvc

import gvc.parser.Parser
import fastparse.Parsed.{Failure, Success}
import gvc.analyzer._
import gvc.benchmarking.BenchmarkExecutor.injectAndWrite
import gvc.transformer._
import gvc.benchmarking.{
  BaselineChecker,
  BenchmarkExecutor,
  BenchmarkExporter,
  BenchmarkExternalConfig,
  BenchmarkMonitor,
  BenchmarkPopulator,
  BenchmarkRecreator,
  Output,
  Timing
}
import gvc.weaver.{Weaver, WeaverException}
import viper.silicon.Silicon
import viper.silicon.state.{profilingInfo, runtimeChecks}
import viper.silver.ast.Program
import viper.silver.verifier

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import java.io.IOException
import sys.process._
import scala.language.postfixOps
import viper.silicon.state.BranchCond

case class OutputFileCollection(
    baseName: String,
    irFileName: String,
    silverFileName: String,
    c0FileName: String,
    profilingName: String,
    binaryName: String
)

object Main extends App {
  object Defaults {
    val outputFileCollection: OutputFileCollection = getOutputCollection(
      "./temp")
    val includeDirectories: List[String] = List(
      Paths.get("src/main/resources").toAbsolutePath.toString + '/')
  }

  def getOutputCollection(sourceFile: String): OutputFileCollection = {
    val baseName =
      if (sourceFile.toLowerCase().endsWith(".c0"))
        sourceFile.slice(0, sourceFile.length() - 3)
      else sourceFile
    val irFileName = baseName + ".ir.c0"
    val silverFileName = baseName + ".vpr"
    val c0FileName = baseName + ".verified.c0"
    val profilingName = baseName + ".prof.out"
    val binaryName = baseName + ".bin"
    OutputFileCollection(
      baseName,
      irFileName,
      silverFileName,
      c0FileName,
      profilingName,
      binaryName
    )
  }

  val cmdConfig = Config.fromCommandLineArgs(args.toList)

  cmdConfig.validate()
  run(cmdConfig)

  def run(config: Config): Unit = {
    val linkedLibraries =
      config.linkedLibraries ++ Defaults.includeDirectories

    config.mode match {
      case Config.Monitor =>
        val benchConfig =
          BenchmarkExternalConfig.parseMonitor(config)
        BenchmarkMonitor.monitor(benchConfig)
      case Config.DynamicVerification | Config.FramingVerification =>
        Output.printTiming(() => {
          val fileNames = getOutputCollection(config.sourceFile.get)
          val inputSource = readFile(config.sourceFile.get)
          val onlyFraming = config.mode == Config.FramingVerification
          val ir = generateIR(inputSource, linkedLibraries)
          BaselineChecker.check(ir, onlyFraming)
          val outputC0Source = Paths.get(fileNames.c0FileName)
          val outputBinary = Paths.get(fileNames.binaryName)
          injectAndWrite(IRPrinter.print(ir, includeSpecs = false),
                         outputC0Source)
          Timing.compileTimed(outputC0Source, outputBinary, config)
          Timing.execTimed(outputBinary,
                           List(s"--stress ${config.stressLevel.getOrElse(1)}"))
        })
      case Config.Recreate =>
        val benchConfig =
          BenchmarkExternalConfig.parseRecreator(config)
        Output.info(
          s"Recreating permutation ID=${benchConfig.permToRecreate}...")
        val recreated =
          BenchmarkRecreator.recreate(benchConfig, config, linkedLibraries)
        Output.success(
          s"Successfully recreated permutation ID=${benchConfig.permToRecreate}!")
        
        recreated match {
          case BenchmarkRecreator.RecreatedUnverified(ir) =>
            val recreationName = s"./recreated_${benchConfig.permToRecreate}.c0"
            Output.info(s"Writing to $recreationName")
            val inputSource = IRPrinter.print(ir, includeSpecs = true)
            val sourcePath =
              Paths.get(recreationName)
            Files.writeString(sourcePath, inputSource)
            val fileNames = getOutputCollection(recreationName)
            Output.printTiming(() => {
              val verifiedOutput = verify(inputSource, fileNames, cmdConfig)
              execute(verifiedOutput.c0Source, fileNames)
            })
          case BenchmarkRecreator.RecreatedVerified(c0) =>
            val recreationName =
              s"./recreated_${benchConfig.permToRecreate}.verified.c0"
            Output.info(s"Writing to $recreationName")
            val sourcePath =
              Paths.get(recreationName)
            Files.writeString(sourcePath, c0)
            val fileNames = getOutputCollection(recreationName)
            execute(c0, fileNames)
        }
      case Config.Execute =>
        val benchConfig =
          BenchmarkExternalConfig.parseExecutor(config)
        BenchmarkExecutor.execute(benchConfig, config, linkedLibraries)

      case Config.Export =>
        val exportConfig = BenchmarkExternalConfig.parseExport(config)
        BenchmarkExporter.export(exportConfig)

      case Config.Populate =>
        val benchConfig =
          BenchmarkExternalConfig.parsePopulator(config)
        BenchmarkPopulator.populate(benchConfig, linkedLibraries)

      case Config.DefaultMode =>
        val fileNames = getOutputCollection(config.sourceFile.get)
        val inputSource = readFile(config.sourceFile.get)
        Output.printTiming(() => {
          val verifiedOutput = verify(inputSource, fileNames, cmdConfig)
          execute(verifiedOutput.c0Source, fileNames)
        })
      case _ =>
    }
  }

  def readFile(file: String): String =
    try {
      Files.readString(Paths.get(file))
    } catch {
      case _: IOException => Config.error(s"Could not read file 'file'")
    }

  def writeFile(file: String, contents: String): Unit =
    try {
      Files.writeString(Paths.get(file), contents, StandardCharsets.UTF_8)
    } catch {
      case _: IOException => Config.error(s"Could not write file '$file'")
    }

  def deleteFile(file: String): Unit =
    try {
      Files.delete(Paths.get(file))
    } catch {
      case _: IOException => Config.error(s"Could not delete file 'file'")
    }

  def dump(output: String): Nothing = {
    println(output)
    sys.exit(0)
  }

  def dumpC0(output: String): Nothing = {
    // Print runtime check information for debugging when dumping C0 output
    // This only happens after verification, so runtime checks have been initialized

    for ((exp, checks) <- viper.silicon.state.runtimeChecks.getChecks) {
      println("Runtime checks required for " + exp.toString + ":")
      println(
        checks
          .map(b =>
            s"  if ${if (b.branchInfo.isEmpty) "true"
            else
              b.branchInfo
                .map { case BranchCond(branch, _, _) => branch }
                .map(c => "(" + c.toString() + ")")
                .mkString(" && ")}: ${b.checks.toString()}")
          .mkString("\n")
      )
    }
    dump(output)
  }

  def generateIR(
      inputSource: String,
      librarySearchPaths: List[String]
  ): IR.Program = {
    val parsed = Parser.parseProgram(inputSource) match {
      case fail: Failure =>
        Config.error(s"Parse error:\n${fail.trace().longAggregateMsg}")
      case Success(value, _) => value
    }
    val errors = new ErrorSink()
    val resolved = Validator
      .validateParsed(parsed, librarySearchPaths, errors)
      .getOrElse(
        Config.error(
          s"Errors:\n" +
            errors.errors.map(_.toString()).mkString("\n")
        )
      )
    IRTransformer.transform(resolved)
  }

  case class VerifiedOutput(
      silver: Program,
      c0Source: String,
      profiling: ProfilingInfo,
      timing: VerifierTiming
  )

  case class VerifierTiming(
      translation: Long,
      verification: Long,
      instrumentation: Long
  )

  case class ProfilingInfo(nConjuncts: Int, nConjunctsEliminated: Int)

  class VerifierException(message: String) extends Exception(message)

  def resolveSilicon(config: Config): Silicon = {
    val reporter = viper.silver.reporter.StdIOReporter()
    val z3Exe = Config.resolveToolPath("z3", "Z3_EXE")
    Silicon.fromPartialCommandLineArguments(
      Seq("--z3Exe", z3Exe, "--checkTimeout", "0"),
      reporter,
      Seq()
    )
  }

  def verify(inputSource: String,
             fileNames: OutputFileCollection,
             config: Config): VerifiedOutput = {
    def silicon = resolveSilicon(config)

    verifySiliconProvided(silicon, inputSource, fileNames, config)
  }

  def verifySiliconProvided(silicon: Silicon,
                            inputSource: String,
                            fileNames: OutputFileCollection,
                            config: Config): VerifiedOutput = {
    profilingInfo.reset
    runtimeChecks.reset

    val translationStart = System.nanoTime()
    val ir =
      generateIR(
        inputSource,
        config.linkedLibraries ++ Defaults.includeDirectories
      )
    val silver = IRSilver.toSilver(ir)
    val translationStop = System.nanoTime()
    val translationTime = translationStop - translationStart

    if (config.dump.contains(Config.DumpIR))
      dump(IRPrinter.print(ir, includeSpecs = true))
    else if (config.saveFiles)
      writeFile(
        fileNames.irFileName,
        IRPrinter.print(ir, includeSpecs = true)
      )
    if (config.dump.contains(Config.DumpSilver)) dump(silver.program.toString())
    else if (config.saveFiles)
      writeFile(fileNames.silverFileName, silver.program.toString())

    val verificationStart = System.nanoTime()
    silicon.start()
    silicon.verify(silver.program) match {
      case verifier.Success => ()
      case verifier.Failure(errors) =>
        val message = errors.map(_.readableMessage).mkString("\n")
        silicon.stop()
        throw VerificationException(message)
    }
    silicon.stop()
    val verificationStop = System.nanoTime()
    val verificationTime = verificationStop - verificationStart

    if (config.onlyVerify) sys.exit(0)

    val weavingStart = System.nanoTime()
    try {
      Weaver.weave(ir, silver)
    } catch {
      case t: Throwable =>
        throw new WeaverException(t.getMessage)
    }
    val weavingStop = System.nanoTime()
    val weavingTime = weavingStop - weavingStart

    val c0Source = IRPrinter.print(ir, includeSpecs = false)
    if (config.dump.contains(Config.DumpC0))
      dumpC0(c0Source)
    VerifiedOutput(
      silver.program,
      c0Source,
      ProfilingInfo(
        profilingInfo.getTotalConjuncts,
        profilingInfo.getEliminatedConjuncts
      ),
      VerifierTiming(
        translationTime,
        verificationTime,
        weavingTime
      )
    )
  }

  def execute(
      verifiedSource: String,
      fileNames: OutputFileCollection
  ): Unit = {
    val outputExe = cmdConfig.output.getOrElse("a.out")

    // TODO: Figure out how we can use the actual resource
    // Since it is bundled in the JAR we have to extract it and put it somewhere

    val cc0Options = CC0Options(
      compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
      saveIntermediateFiles = cmdConfig.saveFiles,
      output = Some(outputExe),
      includeDirs = Defaults.includeDirectories,
      profilingEnabled = cmdConfig.profilingEnabled
    )
    // Always write the intermediate C0 file, but then delete it
    // if not saving intermediate files
    writeFile(fileNames.c0FileName, verifiedSource)
    val compilerExit =
      try {
        CC0Wrapper.exec(fileNames.c0FileName, cc0Options)
      } finally {
        if (!cmdConfig.saveFiles) deleteFile(fileNames.c0FileName)
      }

    if (compilerExit != 0) Config.error("Compilation failed")

    if (cmdConfig.exec) {
      val outputCommand = Paths.get(outputExe).toAbsolutePath.toString
      sys.exit(Seq(outputCommand) !)
    } else {
      sys.exit(0)
    }
  }
}

case class VerificationException(message: String) extends Exception(message)
