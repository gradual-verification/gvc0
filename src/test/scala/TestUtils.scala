package gvc.specs

import java.nio.file._
import scala.collection.mutable.ListBuffer
import java.io.IOException
import gvc.parser.Parser
import fastparse.Parsed
import gvc.analyzer._
import gvc.transformer._
import gvc.weaver.Weaver
import viper.silver.{ast => vpr}

case class TestProgram(
    ir: IR.Program,
    silverProgram: vpr.Program
) {
  def weave = Weaver.weave(ir, silverProgram)

  def irSource = IRPrinter.print(ir, true)

  def silverSource = silverProgram.toString()
}

case class TestResource(file: Path) {
  def read(): String =
    Files.readString(file)

  def update(contents: String) = {
    val relativePath = TestUtils.resourcesRoot.relativize(file.toAbsolutePath())
    val resourcePath = TestUtils.resourcesSourceRoot.resolve(relativePath)
    Files.writeString(resourcePath, contents)
  }
}

// This encapsulates the pattern of grouping input and expected output
// files. Files such as `input.c`, `input.output.c`, `input.txt` will all
// be grouped together so that a single test can process the group of files.
// Note that the name is assumed to be relative to the `resourcesRoot`.
class FileCollection(val name: String) {
  // ID that can be used for filenames
  val id = name.replace(FileSystems.getDefault.getSeparator(), "_")

  def apply(ext: String): TestResource =
    get(ext).getOrElse(throw new Exception(s"Could not find '${name + ext}'"))

  def get(ext: String): Option[TestResource] = {
    val file = TestUtils.resourcesRoot.resolve(name + ext)
    if (Files.exists(file))
      Some(TestResource(file))
    else
      None
  }
}

class ProgramException(message: String) extends Exception(message)
class ParserException(message: String) extends ProgramException(message)
class ResolverException(message: String) extends ProgramException(message)
class TypeCheckerException(message: String) extends ProgramException(message)
class ValidatorException(message: String) extends ProgramException(message)

object TestUtils {
  val resourcesRoot = Paths.get(getClass.getResource("/").toURI())
  val resourcesSourceRoot = Paths.get("src/test/resources")

  def getAllFiles(dir: Path): List[Path] = {
    val files = ListBuffer[Path]()
    Files.walkFileTree(
      dir.toAbsolutePath(),
      new SimpleFileVisitor[Path] {
        override def visitFile(
            file: Path,
            attrs: attribute.BasicFileAttributes
        ): FileVisitResult = {
          files += file.toAbsolutePath()
          FileVisitResult.CONTINUE
        }
      }
    )
    files.toList
  }

  // This basename operates differently to normal basename:
  // It does not remove the directory
  // It strips multiple "extensions", i.e. `root.a.b.c` -> `root`
  def basename(file: Path): String = {
    file.toString().replaceFirst("\\.[^/\\\\]*$", "")
  }

  // Groups files by their basename (see notes on modified basename)
  def groupFiles(files: List[Path]): List[FileCollection] =
    files
      .groupBy(basename(_))
      .map { case (base, _) => new FileCollection(base) }
      .toList

  def groupResources(directory: String): List[FileCollection] = {
    groupFiles(
      getAllFiles(resourcesRoot.resolve(directory))
        .map(f => resourcesRoot.relativize(f))
    )
  }

  def deleteDirectory(dir: Path): Unit = {
    Files.walkFileTree(
      dir,
      new SimpleFileVisitor[Path] {
        override def postVisitDirectory(
            dir: Path,
            exc: IOException
        ): FileVisitResult = {
          Files.delete(dir)
          FileVisitResult.CONTINUE
        }
        override def visitFile(
            file: Path,
            attrs: attribute.BasicFileAttributes
        ): FileVisitResult = {
          Files.delete(file)
          FileVisitResult.CONTINUE
        }
      }
    )
  }

  // Utility for parsing and generating a complete program, both IR and Silver
  def program(source: String): TestProgram = {
    val parsed = Parser.parseProgram(source) match {
      case fail: Parsed.Failure =>
        throw new ParserException(fail.trace().longMsg)
      case Parsed.Success(p, _) => p
    }

    val sink = new ErrorSink()
    def getErrors = sink.errors.map(_.message).mkString("\n")

    val result =
      Resolver.resolveProgram(parsed, List("./src/main/resources/"), sink)
    if (!sink.errors.isEmpty)
      throw new ResolverException(getErrors)

    TypeChecker.check(result, sink)
    if (!sink.errors.isEmpty)
      throw new TypeCheckerException(getErrors)

    AssignmentValidator.validate(result, sink)
    ReturnValidator.validate(result, sink)
    SpecificationValidator.validate(result, sink)
    ImplementationValidator.validate(result, sink)
    if (!sink.errors.isEmpty)
      throw new ValidatorException(getErrors)

    val ir = IRTransformer.transform(result)
    val silver = IRSilver.toSilver(ir)

    TestProgram(ir, silver)
  }
}
