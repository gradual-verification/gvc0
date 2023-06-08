package gvteal.specs.integration

import org.scalatest.funsuite.AnyFunSuite
import java.lang.ProcessBuilder.Redirect

import gvteal.specs._
import org.scalatest._
import java.nio.file._
import gvteal.specs.BaseFileSpec
import scala.io.Source

class CompilerSpec extends AnyFunSuite with BaseFileSpec with ParallelTestExecution {
  var output: Path = null
  val javaArgs = List("-Xss15m")

  override protected def withFixture(test: NoArgTest): Outcome = {
    try {
      output = Files.createTempDirectory("gvc0")
      super.withFixture(test)
    } finally {
      TestUtils.deleteDirectory(output)
    }
  }

  def compile(args: String*): Unit = {
    val jvm = ProcessHandle.current().info().command().get()
    val mainClass = "gvteal.Main"

    val command = jvm :: javaArgs ::: "-classpath" :: getClasspath :: mainClass :: args.toList
    execute(command:_*)
  }

  def execute(command: String*): Unit = {
    val proc = new ProcessBuilder(command:_*)
      .redirectError(Redirect.INHERIT)
      .redirectOutput(Redirect.PIPE)
      .start()

    val exit = proc.waitFor()
    if (exit != 0) {
      info("Output: " + Source.fromInputStream(proc.getInputStream()).mkString)
      fail(s"Command '${command.mkString(" ")}' exited with code $exit")
    }
  }

  (TestUtils.groupResources("verifier") ++ TestUtils.groupResources("quant-study")).foreach { input =>
    test(s"test ${input.name}") {
      val source = input(".c0").read()
      val id = input.id

      // Copy to temporary directory
      val sourceFile = output.resolve(id + ".c0")
      Files.writeString(sourceFile, source)

      val outputExe = output.resolve(id)
      compile(s"--output=${outputExe}", "--save-files", sourceFile.toString())

      execute(outputExe.toString())

      val verified = Files.readString(output.resolve(id + ".verified.c0"))
      val ir = Files.readString(output.resolve(id + ".ir.c0"))
      val vpr = Files.readString(output.resolve(id + ".vpr"))

      assertFile(input.get(".output.c0"), verified)
      assertFile(input.get(".ir.c0"), ir)
      assertFile(input.get(".vpr"), vpr)
    }
  }
}