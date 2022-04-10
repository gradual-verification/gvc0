package gvc.specs.permutation
import gvc.Config
import gvc.permutation._
import org.scalatest.funsuite.{AnyFunSuite, FixtureAnyFunSuite}

import scala.collection.mutable
import gvc.specs._
import org.scalatest.Outcome

import java.nio.file.{Files, Path}

class PermutationSpec extends FixtureAnyFunSuite {

  test("Runtime check infrastructure") { args =>
    for (input <- TestUtils.groupResources("quant-study")) {
      val tempDir = Files.createTempDirectory("gvc0-permutation-spec")
      val benchConfig =
        BenchConfig.resolveBenchmarkConfig(
          input(".c0").read,
          List("src/main/resources/"),
          Config(compileBenchmark = Some(tempDir.toString))
        )
      val sampler = new Sampler(benchConfig);
      val sampleToPermute =
        sampler.sample(SamplingHeuristic.Random)
      val selector = new SelectVisitor(benchConfig.ir)

      val auxLabeller = new LabelVisitor()
      def labelSet(labels: List[ASTLabel]): Set[String] = {
        labels
          .map(label => {
            val hash = label.toString
            hash.substring(0, hash.lastIndexOf('.'))
          })
          .toSet
      }

      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()

      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val builtPermutation = selector.visit(permutationIndices.toSet)

        val builtLabels = auxLabeller.visit(builtPermutation)
        assert(
          labelSet(builtLabels)
            .diff(labelSet(currentPermutation.toList))
            .isEmpty
        )
      }
      TestUtils.deleteDirectory(tempDir)
    }

  }

  case class Args()
  type FixtureParam = Args

  override protected def withFixture(test: OneArgTest): Outcome = {
    try {
      test(Args())
    } finally {}
  }
}
