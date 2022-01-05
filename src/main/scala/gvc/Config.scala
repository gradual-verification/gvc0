package gvc

import java.nio.file.{Files, Paths}
import java.io.File

sealed trait DumpType

case class Config(
  val dump: Option[DumpType] = None,
  val output: Option[String] = None,
  val saveFiles: Boolean = false,
  val exec: Boolean = false,
  val onlyVerify: Boolean = false,
  val sourceFile: Option[String] = None,
) {
  def validate(): Unit = {
    (
      if (dump.isDefined && output.isDefined) Some("Cannot combine --dump and --output")
      else if (dump.isDefined && exec) Some("Cannot combine --dump and --exec")
      else if (dump.isDefined && onlyVerify) Some("Cannot combine --dump and --only-verify")
      else if (dump.isDefined && saveFiles) Some("Cannot combine --dump and --save-files")
      else if (output.isDefined && onlyVerify) Some("Cannot combine --output and --only-verify")
      else if (exec && onlyVerify) Some("Cannot combine --exec and --only-verify")
      else if (!sourceFile.isDefined) Some("No source file specified")
      else if (!Files.exists(Paths.get(sourceFile.get))) Some(s"Source file '${sourceFile.get}' does not exist")
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
               |  -h         --help           Give short usage message and exit
               |  -d <type>  --dump=<type>    Print the generated code and exit, where <type> specifies
               |                              the type of code to print: ir, silver, c0
               |  -o <file>  --output=<file>  Place the executable output into <file>
               |  -v         --only-verify    Stop after static verification
               |  -s         --save-files     Save the intermediate files produced (IR, Silver, C0, and C)
               |  -x         --exec           Execute the compiled file"""

  private val dumpArg = raw"--dump=(.+)".r
  private val outputArg = raw"--output=(.+)".r

  def error(message: String): Nothing = {
    println(message)
    sys.exit(1)
  }

  private def parseDumpType(t: String) = t.toLowerCase() match {
    case "ir" => DumpIR
    case "silver" => DumpSilver
    case "c0" => DumpC0
    case _ => error(s"Invalid dump output type: $t")
  }

  def fromCommandLineArgs(args: List[String], current: Config = Config()): Config =
    args match {
      case "-d" :: t :: tail => fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case dumpArg(t) :: tail => fromCommandLineArgs(tail, current.copy(dump = Some(parseDumpType(t))))
      case "-o" :: f :: tail => fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case outputArg(f) :: tail => fromCommandLineArgs(tail, current.copy(output = Some(f)))
      case ("-s" | "--save-files") :: tail => fromCommandLineArgs(tail, current.copy(saveFiles = true))
      case ("-x" | "--exec") :: tail => fromCommandLineArgs(tail, current.copy(exec = true))
      case ("-v" | "--only-verify") :: tail => fromCommandLineArgs(tail, current.copy(onlyVerify = true))
      case ("-h" | "--help") :: _ => error(Config.help)
      
      case other :: _ if other.startsWith("-") => error(s"Unrecognized command line argument: $other")
      case sourceFile :: tail => current.sourceFile match {
        case Some(_) => error("Cannot specify multiple input files")
        case None => fromCommandLineArgs(tail, current.copy(sourceFile = Some(sourceFile)))
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
      .orElse(sys.env("PATH")
        .split(File.pathSeparatorChar)
        .map(dir => Paths.get(dir).resolve(name))
        .find(p => Files.exists(p))
        .map(_.toString()))
      .getOrElse(error(s"Unable to locate a $name executable"))
  }
}