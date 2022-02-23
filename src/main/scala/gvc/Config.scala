package gvc

import gvc.visualizer.{PermuteMode}
import gvc.visualizer.PermuteMode.PermuteMode
import gvc.visualizer.PermuteTarget.{All, Field, Expr, Predicate, PermuteTarget}

import java.nio.file.{Files, Paths}
import java.io.File
import scala.annotation.tailrec

sealed trait DumpType

case class Config(
    dump: Option[DumpType] = None,
    output: Option[String] = None,
    permute: Option[String] = None,
    permuteExclude: Option[String] = None,
    permuteModes: Map[PermuteTarget, PermuteMode] = Map(),
    permuteTikz: Option[String] = None,
    permuteDumpDir: Option[String] = None,
    saveFiles: Boolean = false,
    exec: Boolean = false,
    onlyVerify: Boolean = false,
    sourceFile: Option[String] = None
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
      else if (
        permute.isDefined && permuteExclude.isDefined && !Files.exists(
          Paths.get(permuteExclude.get)
        )
      )
        Some(
          s"Permutation exclusion list '${permuteExclude.get}' does not exist'"
        )
      else if (permute.isEmpty && permuteExclude.isDefined)
        Some(s"Option --permute must be enabled to use --permute-exclude")
      else if (permute.isEmpty && permuteModes.nonEmpty)
        Some(s"Option --permute must be enabled to use --permute-mode")
      else if (permute.isEmpty && permuteTikz.isDefined)
        Some(s"Option --permute must be enabled to use --permute-tikz")
      else if (permute.isEmpty && permuteDumpDir.isDefined)
        Some(s"Option --permute must be enabled to use --permute-dump-dir")
      else if (permuteDumpDir.isDefined && dump.isEmpty)
        Some(s"Option --permute-dump-dir must be used with --dump")
      else if (
        permuteDumpDir.isDefined && !Files.exists(Paths.get(permuteDumpDir.get))
      )
        Some(s"The specified directory for --permute-dump-dir doesn't exist.")
      else None
    ).foreach(Config.error)
  }
}

object Config {
  case object DumpIR extends DumpType
  case object DumpSilver extends DumpType
  case object DumpC0 extends DumpType

  val help = """Usage: gvc0 [OPTION...] SOURCEFILE
               |where OPTION is
               |  -h         --help                         Give short usage message and exit
               |  -d <type>  --dump=<type>                  Print the generated code and exit, where <type> specifies
               |                                            the type of code to print: ir, silver, c0
               |  -o <file>  --output=<file>                Place the executable output into <file>
               |  -v         --only-verify                  Stop after static verification
               |  -s         --save-files                   Save the intermediate files produced (IR, Silver, C0, and C)
               |  -x         --exec                         Execute the compiled file
               |  -p <file>  --perm=<file>                  Generate, verify, execute, and profile all permutations of specs for a program,
               |                                            saving the output to <file> in .csv format.
               |             --perm-ex=<file>               Provide a comma-separated list of methods to keep constant in all permutations.
               |             --perm-tikz=<file>             Specify the location to save a LaTeX-formatted lattice diagram of runtime statistics.
               |             --perm-dump-dir=<dir>          Specify the directory to dump permuted programs, if --dump is enabled.
               |             --perm-all=<mode>              Specify 'exp', 'linear'. Linear is chosen by default.
               |             --perm-field=<mode>            Set the permutation mode for field access predicates. 
               |             --perm-pred=<mode>             Set the permutation mode for user-defined predicates.
               |             --perm-expr=<mode>             Set the permutation mode for non-predicate expressions in specifications."""
  private val dumpArg = raw"--dump=(.+)".r
  private val outputArg = raw"--output=(.+)".r
  private val permuteArg = raw"--perm=(.+)".r
  private val permuteExcludeArg = raw"--perm-exclude=(.+)".r
  private val permuteAllArg = raw"--perm-all=(.+)".r
  private val permuteTikzArg = raw"--perm-tikz=(.+)".r
  private val permuteDumpDir = raw"--perm-dump-dir=(.+)".r
  private val permuteFieldMode = raw"--perm-field=(.+)".r
  private val permutePredicateMode = raw"--perm-pred=(.+)".r
  private val permuteExprMode = raw"--perm-expr=(.+)".r
  def error(message: String): Nothing = {
    println(message)
    sys.exit(1)
  }

  private def parseDumpType(t: String) = t.toLowerCase() match {
    case "ir"     => DumpIR
    case "silver" => DumpSilver
    case "c0"     => DumpC0
    case _        => error(s"Invalid dump output type: $t")
  }

  def parsePermuteMode(str: String): PermuteMode = str.toLowerCase() match {
    case "exp"    => PermuteMode.Linear
    case "linear" => PermuteMode.Exp
    case _        => error(s"Invalid permute mode type: $str")
  }

  @tailrec
  def fromCommandLineArgs(
      args: List[String],
      current: Config = Config()
  ): Config =
    args match {
      case "-d" :: t :: tail =>
        fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case dumpArg(t) :: tail =>
        fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case "-o" :: f :: tail =>
        fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case "-p" :: f :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(
            permute = Some(f),
            permuteModes = current.permuteModes + (All -> PermuteMode.Append)
          )
        )
      case outputArg(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case permuteArg(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(
            permute = Some(f),
            permuteModes = current.permuteModes + (All -> PermuteMode.Append)
          )
        )
      case permuteExcludeArg(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(permuteExclude = Some(f)))
      case permuteTikzArg(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(permuteTikz = Some(f)))
      case permuteDumpDir(f) :: tail =>
        fromCommandLineArgs(tail, current.copy(permuteDumpDir = Some(f)))
      case permuteAllArg(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(permuteModes =
            current.permuteModes + (All -> parsePermuteMode(f))
          )
        )
      case permuteFieldMode(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(permuteModes =
            current.permuteModes + (Field -> parsePermuteMode(f))
          )
        )
      case permutePredicateMode(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(permuteModes =
            current.permuteModes + (Predicate -> parsePermuteMode(f))
          )
        )
      case permuteExprMode(f) :: tail =>
        fromCommandLineArgs(
          tail,
          current.copy(permuteModes =
            current.permuteModes + (Expr -> parsePermuteMode(f))
          )
        )
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
