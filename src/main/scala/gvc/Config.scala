package gvc
import java.nio.file.{Files, Paths}
import java.io.File
import scala.annotation.tailrec

sealed trait DumpType
sealed trait Mode

case class Config(
    dump: Option[DumpType] = None,
    output: Option[String] = None,
    timeout: Option[Long] = None,
    compileBenchmark: Option[String] = None,
    compileStressTest: Option[String] = None,
    mode: Mode = Config.DefaultMode,
    benchmarkPaths: Option[Int] = None,
    benchmarkStress: Boolean = false,
    benchmarkWStep: Option[Int] = None,
    benchmarkWUpper: Option[Int] = None,
    benchmarkIterations: Option[Int] = None,
    benchmarkWList: Option[List[Int]] = None,
    benchmarkSkipVerification: Boolean = false,
    disableBaseline: Boolean = false,
    saveFiles: Boolean = false,
    exec: Boolean = false,
    onlyVerify: Boolean = false,
    sourceFile: Option[String] = None,
    linkedLibraries: List[String] = List.empty
) {
  def validate(): Unit = {
    (
      if (dump.isDefined && output.isDefined)
        Some("Cannot combine --dump and --output")
      else if (dump.isDefined && exec) Some("Cannot combine --dump and --exec")
      else if (dump.isDefined && onlyVerify)
        Some("Cannot combine --dump and --only-verify")
      else if (dump.isDefined && saveFiles)
        Some("Cannot combine --dump and --save-files")
      else if (output.isDefined && onlyVerify)
        Some("Cannot combine --output and --only-verify")
      else if (exec && onlyVerify)
        Some("Cannot combine --exec and --only-verify")
      else if (sourceFile.isEmpty) Some("No source file specified")
      else if (!Files.exists(Paths.get(sourceFile.get)))
        Some(s"Source file '${sourceFile.get}' does not exist")
      else if (disableBaseline && compileBenchmark.isEmpty)
        Some(
          s"Benchmarking (--benchmark) must be enabled to use --disable-baseline."
        )
      else if (
        benchmarkPaths.isDefined && compileBenchmark.isEmpty && compileStressTest.isEmpty
      )
        Some(
          s"Benchmarking (--benchmark) or stress testing (--stress) must be enabled to use -p or --paths."
        )
      else if (
        benchmarkWStep.isDefined && compileBenchmark.isEmpty && compileStressTest.isEmpty
      )
        Some(
          s"Benchmarking (--benchmark) or stress testing (--stress) must be enabled to use --step"
        )
      else if (
        benchmarkWUpper.isDefined && compileBenchmark.isEmpty && compileStressTest.isEmpty
      )
        Some(
          s"Benchmarking (--benchmark) or stress testing (--stress) must be enabled to use --upper."
        )
      else if (
        benchmarkIterations.isDefined && compileBenchmark.isEmpty && compileStressTest.isEmpty
      )
        Some(
          s"Benchmarking (--benchmark) or stress testing (--stress) must be enabled to use -i/--iter."
        )
      else if (
        (benchmarkWStep.isDefined || benchmarkWUpper.isDefined) && benchmarkWList.isDefined
      )
        Some(
          s"Either provide a list of specific stress levels (--w-list), or set a step size (--w-step) and/or upper bound (--w-upper)."
        )
      else None
    ).foreach(Config.error)
  }
}

object Config {
  case object DumpIR extends DumpType
  case object DumpSilver extends DumpType
  case object DumpC0 extends DumpType
  case object StressMode extends Mode
  case object BenchmarkMode extends Mode
  case object DefaultMode extends Mode

  val help = """Usage: gvc0 [OPTION...] SOURCEFILE
               |where OPTION is
               |  -h            --help                         Give short usage message and exit
               |  -d <type>     --dump=<type>                  Print the generated code and exit, where <type> specifies
               |                                               the type of code to print: ir, silver, c0
               |  -o <file>     --output=<file>                Place the executable output into <file>
               |  -v            --only-verify                  Stop after static verification
               |  -s            --save-files                   Save the intermediate files produced (IR, Silver, C0, and C)
               |  -x            --exec                         Execute the compiled file
               |  -b <dir>      --benchmark=<dir>              Generate all files required for benchmarking to the specified directory.
               |                --paths=<n>                    Specify how many paths through the lattice of permutations to sample. Default is 1.
               |                --disable-baseline             Speedup benchmark generation by skipping the baseline.
               |                --only-exec                    For benchmark directories that already exist, skip verification entirely and execute the programs that are present. 
               |                --iter=<n>                     Specify the number of iterations for execution.
               |  -t <n(s|m)>   --timeout=<n(s|m)>             Specify a timeout for the verifier in seconds (s) or minutes (m).
               |  
               |                --stress=<dir>                 Perform a stress test of full dynamic verification, comparing performance against the unverified source program.
               |
               |                --w-step=<n>                   Specify the step size of the stress factor from 0 to the upper bound.
               |                --w-upper=<n>                  Specify the upper bound on the stress factor.
               |                --w-list=<n,...>            Specify a list of stress levels to execute."""

  private val dumpArg = raw"--dump=(.+)".r
  private val outputArg = raw"--output=(.+)".r
  private val benchmarkDir = raw"--benchmark=(.+)".r
  private val paths = raw"--paths=(.+)".r
  private val stepSize = raw"--w-step=(.+)".r
  private val upperBound = raw"--w-upper=(.+)".r
  private val specifyIncrements = raw"--w-list=(.+)".r
  private val iterationArg = raw"--iter=(.+)".r
  private val timeoutArg = raw"--timeout=(.+)".r
  private val stressArg = raw"--stress=(.+)".r
  private val timeoutSec = raw"([0-9]+)s".r
  private val timeoutMin = raw"([0-9]+)m".r

  def error(message: String): Nothing = {
    println(message)
    sys.exit(1)
  }

  private def parseTimeout(t: String): Long = t match {
    case timeoutSec(t) => t.substring(0, t.length).toLong * 1000
    case timeoutMin(t) => t.substring(0, t.length).toLong * 60 * 1000
    case _             => error(s"Invalid timeout: $t")
  }

  private def parseDumpType(t: String) = t.toLowerCase() match {
    case "ir"     => DumpIR
    case "silver" => DumpSilver
    case "c0"     => DumpC0
    case _        => error(s"Invalid dump output type: $t")
  }

  private def parseIntList(t: String): List[Int] = {
    if (t.matches("[0-9]+(,[0-9]+)+")) {
      t.split(',').map(s => s.trim.toInt).toList
    } else {
      error(
        s"Invalid input for --w-list; expected a comma-separated list of integers"
      )
    }
  }

  @tailrec
  def fromCommandLineArgs(
      args: List[String],
      current: Config = Config()
  ): Config =
    args match {
      case "--only-exec" :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkSkipVerification = true)
        )
      case specifyIncrements(t) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkWList = Some(parseIntList(t)))
        )
      case "-i" :: t :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkIterations = Some(t.toInt))
        )
      case iterationArg(t) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkIterations = Some(t.toInt))
        )
      case stressArg(t) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(compileStressTest = Some(t), mode = StressMode)
        )
      case "-t" :: t :: tail =>
        fromCommandLineArgs(tail, current.copy(timeout = Some(parseTimeout(t))))
      case timeoutArg(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(timeout = Some(parseTimeout(t))))
      case "-d" :: t :: tail =>
        fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case dumpArg(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case "-o" :: f :: tail =>
        fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case paths(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(benchmarkPaths = Some(f.toInt)))
      case benchmarkDir(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(compileBenchmark = Some(f), mode = BenchmarkMode)
        )
      case "-b" :: f :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(
            compileBenchmark = Some(f),
            mode = BenchmarkMode
          )
        )
      case stepSize(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkWStep = Some(f.toInt))
        )
      case upperBound(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(benchmarkWUpper = Some(f.toInt))
        )
      case outputArg(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case "--disable-baseline" :: tail =>
        fromCommandLineArgs(tail, current.copy(disableBaseline = true))
      case ("-s" | "--save-files") :: tail =>
        fromCommandLineArgs(tail, current.copy(saveFiles = true))
      case ("-x" | "--exec") :: tail =>
        fromCommandLineArgs(tail, current.copy(exec = true))
      case ("-v" | "--only-verify") :: tail =>
        fromCommandLineArgs(tail, current.copy(onlyVerify = true))
      case ("-h" | "--help") :: _ => error(Config.help)
      case other :: _ if other.startsWith("-") =>
        error(s"Unrecognized command line argument: $other")
      case sourceFile :: tail =>
        current.sourceFile match {
          case Some(_) => error("Cannot specify multiple input files")
          case None =>
            fromCommandLineArgs(
              tail,
              current.copy(sourceFile = Some(sourceFile))
            )
        }
      case Nil => current
    }

  def resolveToolPath(name: String, envVar: String): String = {
    // Check if a path is explicitly specified in the environment
    val specified = sys.env.get(envVar)

    // If it is, check that that path exists
    specified
      .filter(p => !Files.exists(Paths.get(p)))
      .foreach(p => error(s"Unable to locate $name at '$p'"))

    // Otherwise, try to resolve it from the directories in PATH
    specified
      .orElse(
        sys
          .env("PATH")
          .split(File.pathSeparatorChar)
          .map(dir => Paths.get(dir).resolve(name))
          .find(p => Files.exists(p))
          .map(_.toString())
      )
      .getOrElse(error(s"Unable to locate a $name executable"))
  }
}
