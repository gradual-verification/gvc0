package weaver

import gvc.Config
import gvc.specs.BaseFileSpec
import org.scalatest.ConfigMap
import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.{Files, Paths}
import sys.process._
import scala.language.postfixOps

class AccessCheckSpec extends AnyFunSuite with BaseFileSpec {
  val dependency = getFile("c0/test.c0")
  val dep: String = Paths.get(getClass.getResource("/c0/test.c0").getPath).toAbsolutePath.toString
  var cc0Path:String = "cc0"
  val cmd = cc0Path + " " + dep + "  -L ./src/main/resources/ -o ./a.out"

  override protected def beforeAll(config: ConfigMap): Unit = {
    super.beforeAll(config)
    val cc0 = Config.resolveToolPath("cc0", "CC0_EXE")
    assert(
      !cc0.isEmpty,
      "Add cc0 to $PATH or configure the CC0_EXE variable with the full path to cc0"
    )
    cc0Path = cc0
    assert(dependency.isDefined,
      "Unable to located c0/test.c0 in test resources directory."
    )
  }

  test("Runtime check infrastructure"){
    val compileExitCode: Int = cmd !

      assert(compileExitCode == 0, "Failed to compile unit tests for runtime check infrastructure.")


    assert(Files.exists(Paths.get("./a.out")), "Unable to locate compiled unit tests. (\'./a.out\')")

    val runExitCode = "./a.out" !

      assert(runExitCode == 0, "Unit tests of runtime check infrastructure failed.")

  }

  override protected def afterAll(config: ConfigMap): Unit = {
    super.afterAll(config)
    Files.delete(Paths.get("./a.out"))

  }
}

