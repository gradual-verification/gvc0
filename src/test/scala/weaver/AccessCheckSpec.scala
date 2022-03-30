package weaver

import gvc.Config
import java.nio.file._
import gvc.specs._
import org.scalatest.Outcome
import org.scalatest.funsuite.FixtureAnyFunSuite
import java.lang.ProcessBuilder
import scala.io.Source

class AccessCheckSpec extends FixtureAnyFunSuite {
  case class Args(cc0: String, tempDir: Path)
  type FixtureParam = Args

  override protected def withFixture(test: OneArgTest): Outcome = {
    val cc0 = Config.resolveToolPath("cc0", "CC0_EXE")
    assert(
      !cc0.isEmpty,
      "Add cc0 to $PATH or configure the CC0_EXE variable with the full path to cc0"
    )

    val tempDir = Files.createTempDirectory("gvc0_access_spec")
    try {
      test(Args(cc0, tempDir))
    } finally {
      TestUtils.deleteDirectory(tempDir)
    }
  }

  test("Runtime check infrastructure") { args =>
    val tempFile = args.tempDir.resolve("test.c0")
    val tempExe = args.tempDir.resolve("test")
    Files.copy(TestUtils.resourcesRoot.resolve("c0/test.c0"), tempFile)

    val compile = new ProcessBuilder(
      args.cc0,
      tempFile.toString,
      "-L", "src/main/resources/",
      "-o", tempExe.toString
    )

    val compileExitCode: Int = compile
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .redirectOutput(ProcessBuilder.Redirect.INHERIT)
      .start()
      .waitFor()

    assert(
      compileExitCode == 0,
      "Failed to compile unit tests for runtime check infrastructure."
    )

    val run = new ProcessBuilder(tempExe.toString())
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .redirectOutput(ProcessBuilder.Redirect.PIPE)
      .start()

    val runExitCode = run.waitFor()
    if (runExitCode != 0)
      info("Output: " + Source.fromInputStream(run.getInputStream()).mkString)
    assert(runExitCode == 0, "Unit tests of runtime check infrastructure failed.")
  }
}
