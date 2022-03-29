package gvc.specs.permutation
import gvc.permutation._
import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable
import gvc.specs._

class PermutationSpec extends AnyFunSuite {
  for (input <- TestUtils.groupResources("quant-study")) {
    // TODO: Fix this test
    ignore("permute " + input.name) {
      val program = TestUtils.program(input(".c0").read)
      val selector = new SelectVisitor(program.ir)
      val labeller = new LabelVisitor()
      val labels = labeller.visit(program.ir)
      val sampleToPermute =
        LabelTools.sample(labels, SamplingHeuristic.Random)
      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()
      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val baseHash =
          LabelTools.hashPermutation(currentPermutation.toList)
        val builtPermutation = selector.visit(permutationIndices)
        val labels = labeller.visit(builtPermutation)
        assert(LabelTools.hashPermutation(labels) == baseHash)
      }
    }
  }
}
