package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.Binary

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

case class PermutedProgram(
    ir: IRGraph.Program,
    nClausesPreconditions: Int,
    nClausesPostconditions: Int,
    nClausesAssertions: Int,
    nCLausesLoopInvariants: Int,
    methodMetadata: Map[IRGraph.Method, PermutedMethod]
)

case class PermutedExpression(
    nClauses: Int,
    expr: Option[IRGraph.Expression]
)

case class PermutationMetadata(
    nClausesPreconditions: Int,
    nClausesPostconditions: Int
)

case class PermutedMethod(
    method: IRGraph.Method,
    nClausesPreconditions: Int,
    nClausesPostconditions: Int,
    nClausesAssertions: Int,
    nClausesLoopInvariants: Int
)

case class PermutedBlock(
    nClausesAssertions: Int,
    nClausesLoopInvariants: Int,
    opList: List[IRGraph.Op]
)

case class PermutedPredicate(
    predicate: IRGraph.Predicate,
    nClauses: Int
)

case class PermutedOp(
    nClausesAssertions: Int = 0,
    nCLausesLoopInvariants: Int = 0,
    op: Option[IRGraph.Op] = None
)

object Gradualizer {

  class GradualizerException(val message: String) extends RuntimeException {
    override def getMessage: String = message
  }
  def crossJoin[T](list: List[List[T]]): List[List[T]] = {
    list match {
      case Nil       => Nil
      case xs :: Nil => xs map (List(_))
      case x :: xs =>
        for {
          i <- x
          j <- crossJoin(xs)
        } yield List(i) ++ j
    }
  }

  def gradualizeProgram(
      program: IRGraph.Program
  ): List[PermutedProgram] = {

    val programPermutations: ListBuffer[PermutedProgram] = ListBuffer()

    val methodPermutations: List[List[PermutedMethod]] = permuteMethods(
      program.methods
    )
    val predicatePermutations: List[List[PermutedPredicate]] =
      permutePredicates(
        program.predicates
      )

    for (methodList <- methodPermutations) {
      for (predicateList <- predicatePermutations) {
        var nClausesPreconditions = 0
        var nClausesPostconditions = 0
        var nClausesAssertions = 0
        var nClausesLoopInvariants = 0
        var nClausesPredicates = 0
        val methodMetadata = mutable.Map[IRGraph.Method, PermutedMethod]()

        val methodsToAdd = methodList.map(permMethod => {
          nClausesPreconditions += permMethod.nClausesPreconditions
          nClausesPostconditions += permMethod.nClausesPostconditions
          nClausesAssertions += permMethod.nClausesAssertions
          nClausesLoopInvariants += permMethod.nClausesLoopInvariants
          methodMetadata += (permMethod.method -> permMethod)
          permMethod.method
        })
        val predicatesToAdd = predicateList.map(permPredicate => {
          nClausesPredicates += permPredicate.nClauses
          permPredicate.predicate
        })

        val clonedProgram: IRGraph.Program =
          program.copy(methodsToAdd, predicatesToAdd)

        programPermutations += PermutedProgram(
          clonedProgram,
          nClausesPreconditions,
          nClausesPostconditions,
          nClausesAssertions,
          nClausesLoopInvariants,
          methodMetadata.toMap
        )
      }
    }
    programPermutations.toList
  }

  def permuteMethods(
      methods: Seq[IRGraph.Method]
  ): List[List[PermutedMethod]] = {
    val perMethodPermutations: ListBuffer[List[PermutedMethod]] =
      ListBuffer()
    methods.foreach(method => {
      val permutedPreconditions = permuteConjunctiveClauses(method.precondition)
      val permutedPostconditions =
        permuteConjunctiveClauses(method.postcondition)
      val permutedMethodBodies = permuteBlock(method.body)

      val methodPermutations = ListBuffer[PermutedMethod]()
      permutedPostconditions.foreach(post => {
        permutedPreconditions.foreach(pre => {
          permutedMethodBodies.foreach(body => {
            val permutation = new IRGraph.Method(method.name, method.returnType)
            permutation.precondition = pre.expr
            permutation.postcondition = post.expr
            permutation.body = new IRGraph.MethodBlock(method)
            permutation.body ++= body.opList

            methodPermutations += PermutedMethod(
              permutation,
              pre.nClauses,
              post.nClauses,
              body.nClausesAssertions,
              body.nClausesLoopInvariants
            )
          })
        })
      })
      perMethodPermutations += methodPermutations.toList
    })

    crossJoin(perMethodPermutations.toList)
  }

  def permutePredicates(
      predicates: Seq[IRGraph.Predicate]
  ): List[List[PermutedPredicate]] = {
    val predicatePermutations = predicates.map(predicate => {
      val permutedPredicateBodies = permuteConjunctiveClauses(
        Some(predicate.expression)
      )
      permutedPredicateBodies.map(body => {
        PermutedPredicate(
          predicate.copy(new IRGraph.Imprecise(body.expr)),
          body.nClauses
        )
      })
    })
    crossJoin(predicatePermutations.toList)
  }
  def permuteBlock(block: IRGraph.Block): List[PermutedBlock] = {
    var currentPermutations: List[PermutedBlock] = List(
      PermutedBlock(0, 0, List())
    )
    val opList = block.toList
    def appendToAll(op: IRGraph.Op): Unit = {
      currentPermutations = currentPermutations.map(prev =>
        PermutedBlock(
          prev.nClausesAssertions,
          prev.nClausesLoopInvariants,
          prev.opList.::(op)
        )
      )
    }

    def permuteToAll(permList: List[PermutedOp]): Unit = {
      currentPermutations = currentPermutations.flatMap(prev => {
        permList.map(curr => {
          PermutedBlock(
            prev.nClausesAssertions + curr.nClausesAssertions,
            prev.nClausesLoopInvariants + curr.nCLausesLoopInvariants,
            if (curr.op.isDefined) prev.opList.::(curr.op.get) else prev.opList
          )
        })
      })
    }

    opList.foreach {
      case fold: IRGraph.Fold => {
        permuteToAll(List(PermutedOp(op = Some(fold)), PermutedOp()))
      }
      case unfold: IRGraph.Unfold => {
        permuteToAll(List(PermutedOp(op = Some(unfold)), PermutedOp()))
      }
      case assert: IRGraph.Assert =>
        if (assert.kind == IRGraph.AssertKind.Specification) {
          permuteToAll(
            permuteConjunctiveClauses(Some(assert.value)).map(expr => {
              PermutedOp(
                nClausesAssertions = expr.nClauses,
                op = Some(
                  new IRGraph.Assert(
                    new IRGraph.Imprecise(expr.expr),
                    IRGraph.AssertKind.Specification
                  )
                )
              )
            })
          )
        } else {
          appendToAll(assert)
        }
      case value: IRGraph.If =>
        val trueBranchPermutations = permuteBlock(value.ifTrue)
        val falseBranchPermutations = permuteBlock(value.ifFalse)
        trueBranchPermutations.flatMap(trueBranch => {
          falseBranchPermutations.map(falseBranch => {
            PermutedOp(
              trueBranch.nClausesAssertions + falseBranch.nClausesAssertions,
              trueBranch.nClausesLoopInvariants + falseBranch.nClausesLoopInvariants,
              Some(value.copy(trueBranch.opList, falseBranch.opList))
            )
          })
        })
      case whl: IRGraph.While =>
        val invariantAssertions = permuteConjunctiveClauses(whl.invariant)
        val whileBodies = permuteBlock(whl.body)
        permuteToAll(
          invariantAssertions.flatMap(invAssert => {
            whileBodies.map(body => {
              PermutedOp(
                body.nClausesAssertions,
                body.nClausesLoopInvariants + invAssert.nClauses,
                Some(whl.copy(invAssert.expr, body.opList))
              )
            })
          })
        )
      case _ => {
        appendToAll(_)
      }
    }
    currentPermutations
  }
  def permuteConjunctiveClauses(
      expression: Option[IRGraph.Expression]
  ): List[PermutedExpression] = {
    var permutedClauses = List[PermutedExpression]()
    expression match {
      case Some(expr: IRGraph.Expression) =>
        val numClausesInAssertion = numClauses(expr)
        val conjunctionNodeIndices = permuteIndices(numClausesInAssertion)
        println(s"There are $numClausesInAssertion clauses")
        conjunctionNodeIndices.foreach(permutation => {
          val subset =
            extractSubsetOfClauses(permutation, currentIndex = 0, expr)
          permutedClauses =
            PermutedExpression(permutation.length, subset) :: permutedClauses
        })
      case None =>
        permutedClauses = PermutedExpression(0, None) :: permutedClauses
    }
    println(
      s"This results in ${permutedClauses.length} permutations of the assertion"
    )
    permutedClauses
  }

  def extractSubsetOfClauses(
      subset: List[Int],
      currentIndex: Int,
      root: IRGraph.Expression
  ): Option[IRGraph.Expression] = {
    if (subset.nonEmpty) {
      root match {
        case binaryRoot: IRGraph.Binary =>
          if (subset.last == currentIndex) {
            val left = extractSubsetOfClauses(
              subset.slice(0, subset.length - 1),
              currentIndex + 1,
              binaryRoot.left
            )
            left match {
              case Some(leftExists: IRGraph.Expression) =>
                Some(
                  new IRGraph.Binary(
                    binaryRoot.operator,
                    leftExists,
                    binaryRoot.right
                  )
                )
              case None => Some(binaryRoot.right)
            }
          } else {
            extractSubsetOfClauses(
              subset,
              currentIndex + 1,
              binaryRoot.left
            )
          }
        case _: IRGraph.Expression =>
          if (subset.last == currentIndex) {
            Some(root)
          } else {
            None
          }
      }
    } else {
      None
    }
  }

  def permute[T](space: List[T]): ListBuffer[List[T]] = {
    val collection = ListBuffer[List[T]]()
    permuteRecurse(space, collection, List(), 0)
    collection
  }

  def permuteIndices(max: Int): ListBuffer[List[Int]] = {
    val collection = ListBuffer[List[Int]]()
    permuteIndexRecurse(max, collection, List(), 0)
    collection
  }

  //https://stackoverflow.com/a/8171776
  def permuteRecurse[T](
      space: List[T],
      collection: ListBuffer[List[T]],
      current: List[T],
      index: Int
  ): Unit = {
    if (index == space.length) {
      collection += current
    } else {
      permuteRecurse(space, collection, space(index) :: current, index + 1)
      permuteRecurse(space, collection, current, index + 1)
    }
  }

  def permuteIndexRecurse(
      max: Int,
      collection: ListBuffer[List[Int]],
      current: List[Int],
      index: Int
  ): Unit = {
    if (index == max) {
      collection += current
    } else {
      permuteIndexRecurse(max, collection, index :: current, index + 1)
      permuteIndexRecurse(max, collection, current, index + 1)
    }
  }

  def numClauses(expr: IRGraph.Expression): Int = {
    var numClauses = 1
    if (expr.isInstanceOf[IRGraph.Binary]) {
      var currExpr = expr
      while (
        (currExpr.isInstanceOf[IRGraph.Binary] && currExpr
          .asInstanceOf[IRGraph.Binary]
          .operator == IRGraph.BinaryOp.And) && currExpr
          .asInstanceOf[IRGraph.Binary]
          .left
          .isInstanceOf[IRGraph.Binary]
      ) {
        numClauses += 1
        currExpr = currExpr.asInstanceOf[Binary].left
      }
    }
    numClauses
  }
}
