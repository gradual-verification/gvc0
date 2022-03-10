package permutation
import gvc.{Config, Main}
import gvc.specs.BaseFileSpec
import gvc.permutation.Permute.{PermuteOutputFiles}
import gvc.permutation.{LabelVisitor, Permute, SamplingHeuristic}
import org.scalatest.ConfigMap
import org.scalatest.funsuite.AnyFunSuite
import java.nio.file.{Files, Paths}
import scala.language.postfixOps
import scala.reflect.io.Directory

class PermutationSpec extends AnyFunSuite with BaseFileSpec {
  val dependency = getFile("quant-study/list.c0")
  val perms = Paths.get("./perms")

  override protected def beforeAll(config: ConfigMap): Unit = {
    super.beforeAll(config)
    assert(
      dependency.isDefined,
      "Unable to located quant-study/list.c0 in test resources directory."
    )
  }

  test("Runtime check infrastructure") {
    val files = PermuteOutputFiles(
      perms,
      Paths.get("./metadata.csv"),
      Paths.get("./mapping.csv")
    )
    val ir = Main.generateIR(dependency.get)
    val visitor = new LabelVisitor()
    val config = new Config(permute = Some(1))
    Permute.exec(
      dependency.get,
      config,
      SamplingHeuristic.Random
    )

    Files
      .list(perms)
      .forEach(path => {
        if (path.getFileName.getFileName.toString.endsWith(".c0")) {
          val contents = Files.readString(path)
          val compareIR = Main.generateIR(contents)
          if (contents.indexOf("/*") >= 0 && contents.indexOf("*/") >= 0) {
            val currentLabels = contents
              .substring(contents.indexOf("/*") + 2, contents.indexOf("*/"))
              .trim()
              .split("\n")
              .map(s => s.substring(0, s.lastIndexOf('.')))
              .toSet

            val compareLabelsObjs = visitor.visit(compareIR)

            val compareLabels = compareLabelsObjs
              .map(obj => obj.hash.substring(0, obj.hash.lastIndexOf('.')))
              .toSet

            assert(
              compareLabels.equals(currentLabels),
              "Permutation ${path.getFileName.toString} didn't match it's labels."
            )
          }
        }
      })
  }

  override protected def afterAll(config: ConfigMap): Unit = {
    super.afterAll(config)
    new Directory(perms.toFile).deleteRecursively()
  }
}
