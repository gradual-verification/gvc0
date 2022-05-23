package gvc.specs.permutation
import gvc.Config
import gvc.permutation._
import gvc.specs._
import gvc.transformer.IR
import gvc.transformer.IR.{Method, Predicate}
import org.scalatest.Outcome
import org.scalatest.funsuite.FixtureAnyFunSuite

import java.nio.file.Files
import scala.collection.mutable

class PermutationSpec extends FixtureAnyFunSuite {
  test(
    "Labels used to generate a permutation match the contents of the result.") {
    _ =>
      for (input <- TestUtils.groupResources("quant-study")) {
        val tempDir = Files.createTempDirectory("gvc0-permutation-spec")
        val benchConfig =
          BenchConfig.resolveBenchmarkConfig(
            input(".c0").read(),
            List("src/main/resources/"),
            Config(compileBenchmark = Some(tempDir.toString))
          )
        val sampler = new Sampler(benchConfig)
        for (_ <- 0 until 4) {
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

          val labelPermutation = new LabelPermutation(benchConfig)

          for (labelIndex <- sampleToPermute.indices) {
            labelPermutation.addLabel(sampleToPermute(labelIndex))

            val builtPermutation = selector.visit(labelPermutation)

            val builtLabels = auxLabeller.visit(builtPermutation)
            assert(
              labelSet(builtLabels.labels)
                .diff(labelSet(labelPermutation.labels.toList))
                .isEmpty
            )
          }
        }
        TestUtils.deleteDirectory(tempDir)
      }
  }
  test("Spec IDs are contiguous") { _ =>
    for (input <- TestUtils.groupResources("quant-study")) {
      val tempDir = Files.createTempDirectory("gvc0-imprecision-spec")
      val benchConfig = BenchConfig.resolveBenchmarkConfig(
        input(".c0").read(),
        List("src/main/resources/"),
        Config(compileBenchmark = Some(tempDir.toString))
      )

      val specIndices =
        benchConfig.labelOutput.labels.map(l => l.specIndex).toSet
      val maxIndex = specIndices.max
      for (index <- 0 until maxIndex)
        assert(specIndices.contains(index))
    }
  }

  test("Each precondition, postcondition, and predicate body has a unique ID") {
    _ =>
      val preconditions = mutable.Map[Method, Int]()
      val postconditions = mutable.Map[Method, Int]()
      val predicateBodies = mutable.Map[Predicate, Int]()
      for (input <- TestUtils.groupResources("quant-study")) {
        val tempDir = Files.createTempDirectory("gvc0-imprecision-spec")
        val benchConfig = BenchConfig.resolveBenchmarkConfig(
          input(".c0").read(),
          List("src/main/resources/"),
          Config(compileBenchmark = Some(tempDir.toString))
        )
        for (label <- benchConfig.labelOutput.labels)
          label.parent match {
            case Left(value) =>
              label.specType match {
                case gvc.permutation.SpecType.Precondition =>
                  assert(!preconditions
                    .contains(value) || preconditions(value) == label.specIndex)
                  preconditions += value -> label.specIndex
                case gvc.permutation.SpecType.Postcondition =>
                  assert(!postconditions
                    .contains(value) || postconditions(value) == label.specIndex)
                  postconditions += value -> label.specIndex
                case _ =>
              }
            case Right(value) =>
              assert(label.specType == SpecType.Predicate)
              assert(
                !predicateBodies
                  .contains(value) || predicateBodies(value) == label.specIndex)
              predicateBodies += value -> label.specIndex
          }
        TestUtils.deleteDirectory(tempDir)
      }
  }

  test("Imprecision removal components are inserted in the correct positions.") {
    _ =>
      for (input <- TestUtils.groupResources("quant-study")) {
        val tempDir = Files.createTempDirectory("gvc0-imprecision-spec")
        val benchConfig = BenchConfig.resolveBenchmarkConfig(
          input(".c0").read(),
          List("src/main/resources/"),
          Config(compileBenchmark = Some(tempDir.toString))
        )
        val sampler = new Sampler(benchConfig)
        for (_ <- 0 until 3) {
          val ordering = sampler.sample(SamplingHeuristic.Random)
          val lastComponents = mutable.Map[Int, (ASTLabel, Int)]()
          val methodCompletionCounts = mutable.Map[IR.Method, Int]()
          val methodCompletedAt = mutable.Map[IR.Method, Int]()
          val imprecisionCount = mutable.Map[Int, Int]()
          val uniqueMethods = mutable.Set[IR.Method]()
          for (labelIndex <- ordering.indices) {
            val label = ordering(labelIndex)
            label.specType match {
              case gvc.permutation.SpecType.Fold |
                  gvc.permutation.SpecType.Unfold =>
                assert(label.parent.isLeft)
                val methodContext = label.parent.left.get
                uniqueMethods += methodContext
                methodCompletionCounts += (methodContext -> (methodCompletionCounts
                  .getOrElse(methodContext, 0) + 1))
                if (methodCompletionCounts.getOrElse(methodContext, 0) == benchConfig.labelOutput
                      .foldUnfoldCount(methodContext))
                  methodCompletedAt(methodContext) = labelIndex
              case gvc.permutation.SpecType.Assert =>
              case _ =>
                lastComponents += label.specIndex -> (label, labelIndex)
            }
            label.exprType match {
              case gvc.permutation.ExprType.Imprecision =>
                imprecisionCount += (label.specIndex -> (imprecisionCount
                  .getOrElse(label.specIndex, 0) + 1))
              case _ =>
            }
          }
          assert(imprecisionCount.values.toSet.size == 1)
          assert(uniqueMethods.size == methodCompletedAt.size)
          val pairList = lastComponents.toList
          for (pair <- pairList) {
            val label = pair._2._1
            label.specType match {
              case gvc.permutation.SpecType.Fold |
                  gvc.permutation.SpecType.Unfold =>
              case _ =>
                assert(label.exprType.equals(ExprType.Imprecision))
                label.parent match {
                  case Left(value) =>
                    val methodCompletionIndex =
                      methodCompletedAt.getOrElse(value, 0)
                    val imprecisionRemovalPoint = pair._2._2
                    assert(methodCompletionIndex < imprecisionRemovalPoint)
                  case Right(_) =>
                }
            }
          }
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
