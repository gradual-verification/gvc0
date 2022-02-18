package gvc.visualizer
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.Binary

import scala.collection.mutable.ListBuffer

object Gradualizer {

  class GradualizerException(val message: String) extends RuntimeException {
    override def getMessage(): String = message
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
  ): List[IRGraph.Program] = {

    val programPermutations: ListBuffer[IRGraph.Program] = ListBuffer()

    val methodPermutations: List[List[IRGraph.Method]] = List()
    val predicatePermutations: List[List[IRGraph.Predicate]] = List()

    for (methodList <- methodPermutations) {
      for (predicateList <- predicatePermutations) {
        val clonedProgram: IRGraph.Program =
          program.clone().asInstanceOf[IRGraph.Program]
        clonedProgram.replaceMethods(methodList)
        clonedProgram.replacePredicates(predicateList)
        programPermutations += clonedProgram
      }
    }
    programPermutations.toList
  }

  def permuteMethods(
      methods: List[IRGraph.Method]
  ): List[List[IRGraph.Method]] = {
    val perMethodPermutations: ListBuffer[List[IRGraph.Method]] =
      ListBuffer()
    methods.foreach(method => {
      val permutedPreconditions = permuteConjunctiveClauses(method.precondition)
      val permutedPostconditions =
        permuteConjunctiveClauses(method.postcondition)
      val permutedMethodBodies = permuteMethodBody(method)

      val methodPermutations = ListBuffer[IRGraph.Method]()
      permutedPostconditions.foreach(post => {
        permutedPreconditions.foreach(pre => {
          permutedMethodBodies.foreach(body => {
            val permutation = method.clone().asInstanceOf[IRGraph.Method]
            permutation.precondition = pre
            permutation.postcondition = post
            permutation.body = body
            methodPermutations += permutation
          })
        })
      })
      perMethodPermutations += methodPermutations
    })
    crossJoin(perMethodPermutations.toList)
  }

  def permuteMethodBody(
      method: IRGraph.Method
  ): List[IRGraph.MethodBlock] =
    permuteBlock(method.body).map(opList => {
      val methodBody = new IRGraph.MethodBlock(method)
      methodBody ++= opList
      methodBody
    })

  def permuteBlock(block: IRGraph.Block): List[List[IRGraph.Op]] = {
    var currentPermutations: List[List[IRGraph.Op]] = List()
    val opList = block.toList
    def appendToAll(op: IRGraph.Op): Unit = {
      currentPermutations = currentPermutations.map(opList => opList.::(op))
    }
    def permuteToAll(permList: List[IRGraph.Op]): Unit = {
      val newPermutations: ListBuffer[List[IRGraph.Op]] = ListBuffer()
      currentPermutations.foreach(opList => {
        for (elem <- permList) { newPermutations += opList.::(elem) }
      })
    }
    opList.foreach {
      case assert: IRGraph.Assert =>
        if (assert.kind == IRGraph.AssertKind.Specification) {
          permuteToAll(
            permuteConjunctiveClauses(Some(assert.value)).map(expr => {
              new IRGraph.Assert(
                new IRGraph.Imprecise(expr),
                IRGraph.AssertKind.Specification
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
            value.copy(trueBranch, falseBranch)
          })
        })
      case whl: IRGraph.While =>
        val invariantAssertions = permuteConjunctiveClauses(whl.invariant)
        val whileBodies = permuteBlock(whl.body)
        permuteToAll(invariantAssertions.flatMap(invAssert => {
          whileBodies.map(body => {
            whl.copy(invAssert, body)
          })
        }))
    }
    currentPermutations
  }
  def permuteConjunctiveClauses(
      expression: Option[IRGraph.Expression]
  ): List[Option[IRGraph.Expression]] = {
    var permutedClauses = List[Option[IRGraph.Expression]]()
    expression match {
      case Some(expr: IRGraph.Expression) =>
        val numClausesInAssertion = numClauses(expr)
        val conjunctionNodeIndices = permuteIndices(numClausesInAssertion)
        println(s"There are $numClausesInAssertion clauses")
        conjunctionNodeIndices.foreach(permutation => {
          val subset =
            extractSubsetOfClauses(permutation, currentIndex = 0, expr)
          permutedClauses = subset :: permutedClauses
        })
      case None => permutedClauses = None :: permutedClauses
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
