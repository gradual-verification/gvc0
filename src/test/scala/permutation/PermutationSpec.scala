package gvc.specs.permutation
import gvc.permutation._
import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable
import gvc.specs._

class PermutationSpec extends AnyFunSuite {
  for (input <- TestUtils.groupResources("quant-study")) {
    val program = TestUtils.program(input(".c0").read)
    val selector = new SelectVisitor(program.ir)
    val labeller = new LabelVisitor()
    val labels = labeller.visit(program.ir)
    val sampler = new Sampler();
    val sampleToPermute =
      sampler.sample(labels, SamplingHeuristic.Random)

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
      val builtLabels = labeller.visit(builtPermutation)
      assert(
        labelSet(builtLabels).diff(labelSet(currentPermutation.toList)).isEmpty
      )
    }
  }
}
