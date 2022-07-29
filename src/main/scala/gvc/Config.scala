package gvc

import gvc.Config.DefaultMode
import gvc.benchmarking.Output

import java.nio.file.{Files, InvalidPathException, Path, Paths}
import java.io.File
import scala.annotation.tailrec

sealed trait DumpType

sealed trait Mode

case class Config(
    dump: Option[DumpType] = None,
    output: Option[String] = None,
    timeout: Option[Long] = None,
    mode: Mode = Config.DefaultMode,
    config: Option[Path] = None,
    onlyExec: Boolean = false,
    saveFiles: Boolean = false,
    exec: Boolean = false,
    onlyVerify: Boolean = false,
    onlyCompile: Boolean = false,
    sourceFile: Option[String] = None,
    linkedLibraries: List[String] = List.empty,
    versionString: Option[String] = None,
    nicknameString: Option[String] = None,
    hardwareString: Option[String] = None,
    dbURLString: Option[String] = None,
    dbUserString: Option[String] = None,
    dbPassString: Option[String] = None,
    recreatePerm: Option[Int] = None,
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
      else if (sourceFile.isEmpty && mode == DefaultMode)
        Some("No source file specified")
      else if (sourceFile.nonEmpty && !Files.exists(Paths.get(sourceFile.get)))
        Some(s"Source file '${sourceFile.get}' does not exist")
      else if (versionString.nonEmpty && versionString.get.trim.isEmpty) {
        Some(s"Invalid version string.")
      } else None
    ).foreach(Config.error)
  }
}

object Config {
  case object DumpIR extends DumpType

  case object DumpSilver extends DumpType

  case object DumpC0 extends DumpType

  case object DefaultMode extends Mode

  case object Populate extends Mode

  case object Execute extends Mode

  case object Recreate extends Mode

  case object Monitor extends Mode

  val help =
    """Usage: gvc0 [OPTION...] SOURCEFILE
      |where OPTION is
      |  -h            --help                         Give short usage message and exit
      |  -d <type>     --dump=<type>                  Print the generated code and exit, where <type> specifies
      |                                               the type of code to print: ir, silver, c0
      |  -o <file>     --output=<file>                Place the executable output into <file>
      |  -v            --only-verify                  Stop after static verification
      |  -s            --save-files                   Save the intermediate files produced (IR, Silver, C0, and C)
      |  -x            --exec                         Execute the compiled file
      |  -t <n(s|m)>   --timeout=<n(s|m)>             Specify a timeout for the verifier in seconds (s) or minutes (m).
      |
      |                --config=<config.xml>          Execute a benchmark using the specified configuration file
      |
      |                --populate                     Populate the benchmarking database using options from the specified configuration file.
      |                --execute                      Execute programs and store results in the database using options from the specified configuration file.
      |                --recreate=<id>                Specify a permutation to recreate from the database  using options from the specified configuration file.
      |
      |                --version=<version>            Specify the version string identifying the current verifier. Overrides config.
      |                --hardware=<hardware>          Specify an identifier for current hardware platform. Overrides config.
      |                --nickname=<nickname>          Specify a nickname for the current hardware platform. Overrides config.

      |                --db-url=<url>                 Specify the URL for the benchmarking database. Overrides config.
      |                --db-user=<username>           Specify the user for the benchmarking database. Overrides config.
      |                --db-pass=<password>           Specify the password for the benchmarking database. Overrides config.
    """

  private val dumpArg = raw"--dump=(.+)".r
  private val outputArg = raw"--output=(.+)".r
  private val timeoutArg = raw"--timeout=(.+)".r
  private val timeoutSec = raw"([0-9]+)s".r
  private val timeoutMin = raw"([0-9]+)m".r
  private val configFileArg = raw"--config=(.+)".r

  private val versionString = raw"--version=(.+)".r
  private val nicknameString = raw"--nickname=(.+)".r
  private val hardwareString = raw"--hardware=(.+)".r

  private val dbURLString = raw"--db-url=(.+)".r
  private val dbUserString = raw"--db-user=(.+)".r
  private val dbPassString = raw"--db-pass=(.+)".r

  private val recreatePermString = raw"--recreate=(.+)".r

  def error(message: String): Nothing = {
    Output.error(message)
    println(message)
    sys.exit(1)
  }

  def prettyPrintException(message: String, throwable: Throwable): Nothing = {
    Output.error(message)
    println(throwable.getMessage)
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

  def parseInt(t: String, config: String): Int = {
    try {
      t.toInt
    } catch {
      case _: NumberFormatException => {
        error(
          s"Invalid option for $config; expected an integer but found '$t'.")
      }
    }
  }

  private def parsePath(p: String,
                        isDir: Boolean = false): java.nio.file.Path = {
    try {
      val toPath = Paths.get(p)
      if (Files.exists(toPath)) {
        if (isDir) {
          if (Files.isDirectory(toPath)) {
            toPath
          } else {
            error(s"Expected a directory, but found a regular file: $p")
          }
        } else {
          if (Files.isRegularFile(toPath)) {
            toPath
          } else {
            error(s"Expected a file, but found a directory: $p")
          }
        }
      } else {
        error(s"File not found: $p")
      }
    } catch {
      case _: InvalidPathException =>
        error(s"Invalid path: $p")
    }
  }

  @tailrec
  def fromCommandLineArgs(
      args: List[String],
      current: Config = Config()
  ): Config =
    args match {
      case hardwareString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(hardwareString = Some(t)))
      case versionString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(versionString = Some(t)))
      case nicknameString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(nicknameString = Some(t)))
      case dbURLString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(dbURLString = Some(t)))
      case dbPassString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(dbPassString = Some(t)))
      case dbUserString(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(dbUserString = Some(t)))
      case "--monitor" :: tail =>
        fromCommandLineArgs(tail, current.copy(mode = Monitor))
      case "--populate" :: tail =>
        fromCommandLineArgs(tail, current.copy(mode = Populate))
      case "--execute" :: tail =>
        fromCommandLineArgs(tail, current.copy(mode = Execute))
      case recreatePermString(t) :: tail =>
        fromCommandLineArgs(tail,
                            current.copy(recreatePerm =
                                           Some(this.parseInt(t, "--recreate")),
                                         mode = Recreate))
      case configFileArg(t) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(config = Some(parsePath(t)))
        )
      case "--only-exec" :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(onlyExec = true)
        )
      case "--only-compile" :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(onlyCompile = true)
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
      case outputArg(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(output = Some(f)))
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
