package permutation

import gvc.{Config, Main}
import gvc.specs.BaseFileSpec
import gvc.visualizer.Permute.{CSVPrinter, PermuteOutputFiles}
import gvc.visualizer.{Labeller, Permute, SamplingHeuristic}
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
    assert(dependency.isDefined,
      "Unable to located quant-study/list.c0 in test resources directory."
    )
  }

  test("Runtime check infrastructure"){
    val files = PermuteOutputFiles(perms, Paths.get("./metadata.csv"), Paths.get("./mapping.csv"))
    val ir = Main.generateIR(dependency.get)
    val labels = Labeller.labelAST(ir)
    val csv = new CSVPrinter(files, labels)


    val config = new Config(permute = Some(10))
    Permute.exec(
      dependency.get,
      config,
      SamplingHeuristic.Random
    )

    Files.list(perms).forEach(path => {
        val compareIR = Main.generateIR(Files.readString(path))
        val compareLabels = Labeller.labelAST(compareIR)
        val currentPermutation = mutable.TreeSet()(Labeller.LabelOrdering)
        compareLabels.foreach(currentPermutation += _)
        val filename = path.getFileName.toString
        val generatedID = filename.substring(filename.lastIndexOf('/') + 1, filename.indexOf(".c0"))
        val compareID = csv.createID(currentPermutation)
        assert(generatedID.equals(compareID), "Generation is incompatible with labelling.")
    })
  }

  override protected def afterAll(config: ConfigMap): Unit = {
    super.afterAll(config)
    new Directory(perms.toFile).deleteRecursively()
  }
}

