package permutation
import gvc.{Config, Main}
import gvc.specs.BaseFileSpec
import gvc.permutation.Permute.{CSVPrinter, PermuteOutputFiles}
import gvc.permutation.{
  LabelException,
  LabelOrdering,
  LabelVisitor,
  Permute,
  SamplingHeuristic
}
import org.scalatest.ConfigMap
import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.{Files, Paths}
import scala.collection.mutable
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
    val labels = visitor.visit(ir)
    val csv = new CSVPrinter(files, labels)

    var totalPrograms = 0
    var totalIncorrect = 0
    val config = new Config(permute = Some(10))
    Permute.exec(
      dependency.get,
      config,
      SamplingHeuristic.Random
    )

    Files
      .list(perms)
      .forEach(path => {
        if (path.getFileName.getFileName.toString.endsWith(".c0")) {
          totalPrograms += 1

          val compareIR = Main.generateIR(Files.readString(path))
          try {
            val compareLabels = visitor.visit(compareIR)
            val currentPermutation = mutable.TreeSet()(LabelOrdering)
            compareLabels.foreach(currentPermutation += _)
            val filename = path.getFileName.toString
            val generatedID = filename
              .substring(filename.lastIndexOf('/') + 1, filename.indexOf(".c0"))
            val compareID = csv.createID(currentPermutation)
            assert(
              generatedID.equals(compareID),
              s"$generatedID =/= $compareID for $filename"
            )
            if (!generatedID.equals(compareID)) totalIncorrect += 1
          } catch {
            case _: LabelException => totalIncorrect += 1
          }
        }
      })
  }

  override protected def afterAll(config: ConfigMap): Unit = {
    super.afterAll(config)
    new Directory(perms.toFile).deleteRecursively()
  }
}
