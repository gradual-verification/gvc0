package gvc.specs.permutation
import gvc.Config
import gvc.permutation._
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.mutable
import gvc.specs._

class PermutationSpec extends AnyFunSuite {
  for (input <- TestUtils.groupResources("quant-study")) {
    val benchConfig =
      BenchConfig.resolveBenchmarkConfig(input(".c0").read, List(), Config())
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
      val builtPermutation = selector.visit(permutationIndices)

      val builtLabels = auxLabeller.visit(builtPermutation)
      assert(
        labelSet(builtLabels).diff(labelSet(currentPermutation.toList)).isEmpty
      )
    }
  }
}
