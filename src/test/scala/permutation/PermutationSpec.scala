package permutation
import fastparse.Parsed.{Failure, Success}
import gvc.analyzer.{ErrorSink, Validator}
import gvc.permutation.{
  LabelOrdering,
  LabelTools,
  LabelVisitor,
  SamplingHeuristic,
  SelectVisitor
}
import gvc.specs.BaseFileSpec
import gvc.transformer.GraphTransformer
import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable

class PermutationSpec extends AnyFunSuite with BaseFileSpec {
  val dependency: Option[String] = getFile("quant-study/list.c0")
  val testFiles: Seq[String] = getFiles("quant-study")
    .filter { name => name.endsWith(".c0") }
  for (name <- testFiles) {
    /*test("test " + name) {
      for (name <- testFiles) {
        val source = getFile(name).get
        gvc.parser.Parser.parseProgram(source) match {
          case _: Failure => fail("could not parse")
          case Success(parsed, _) =>
            val sink = new ErrorSink()
            val result = Validator.validateParsed(parsed, List(), sink)
            assert(sink.errors.isEmpty)
            assert(result.isDefined)
            val ir = GraphTransformer.transform(result.get)
            val selector = new SelectVisitor(ir)
            val labeller = new LabelVisitor()
            val labels = labeller.visit(ir)
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
              assert(LabelTools.hashPermutation(labels).equals(baseHash))
            }
        }
      }
    }*/
  }
}
