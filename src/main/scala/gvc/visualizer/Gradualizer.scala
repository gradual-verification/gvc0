package gvc.visualizer
import gvc.Main.generateIR
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.visualizer.PermuteMode.PermuteMode

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

case class ProgramPermutation(
    ir: IRGraph.Program,
    source: String,
    nClausesPreconditions: Int,
    nClausesPostconditions: Int,
    nClausesAssertions: Int,
    nCLausesLoopInvariants: Int,
    methodMetadata: Map[String, PermutedMethod]
)

case class PermutedExpression(
    nClauses: Int,
    expr: Option[IRGraph.Expression]
)

case class PermutationMetadata(
    nClausesPreconditions: Int,
    nClausesPostconditions: Int
)
object PermuteMode extends Enumeration {
  type PermuteMode = Value
  val Exp, Linear, Field, Predicate = Value
}

case class PermutedMethod(
    method: IRGraph.Method,
    nClausesPreconditions: Int = 0,
    nClausesPostconditions: Int = 0,
    nClausesAssertions: Int = 0,
    nClausesLoopInvariants: Int = 0
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

  def parseMethodExclusionList(rawList: String): Set[String] =
    //TODO: add Regex to verify correct format for method names?
    rawList.split(',').map(_.trim).filter(_.length > 0).toSet

  def gradualizeProgram(
      c0Source: String,
      methodExclusionList: Set[String],
      permuteModeOption: Option[PermuteMode]
  ): List[ProgramPermutation] = {
    val program = generateIR(c0Source)
    val programPermutations: ListBuffer[ProgramPermutation] = ListBuffer()

    val permuteMode = permuteModeOption match {
      case Some(value) => value
      case None        => PermuteMode.Linear
    }
    val methodPermutations: List[List[PermutedMethod]] = permuteMethods(
      program.methods,
      methodExclusionList,
      permuteMode
    )
    val predicatePermutations: List[List[PermutedPredicate]] =
      permutePredicates(
        program.predicates,
        permuteMode
      )

    for (methodList <- methodPermutations) {
      for (predicateList <- predicatePermutations) {
        var nClausesPreconditions = 0
        var nClausesPostconditions = 0
        var nClausesAssertions = 0
        var nClausesLoopInvariants = 0
        var nClausesPredicates = 0
        val methodMetadata = mutable.Map[String, PermutedMethod]()

        val methodsToAdd = methodList.map(permMethod => {
          nClausesPreconditions += permMethod.nClausesPreconditions
          nClausesPostconditions += permMethod.nClausesPostconditions
          nClausesAssertions += permMethod.nClausesAssertions
          nClausesLoopInvariants += permMethod.nClausesLoopInvariants
          methodMetadata += (permMethod.method.name -> permMethod)
          permMethod.method
        })
        val predicatesToAdd = predicateList.map(permPredicate => {
          nClausesPredicates += permPredicate.nClauses
          permPredicate.predicate
        })

        val clonedProgram: IRGraph.Program =
          program.copy(methodsToAdd, predicatesToAdd)

        programPermutations += ProgramPermutation(
          clonedProgram,
          GraphPrinter.print(clonedProgram, includeSpecs = true),
          nClausesPreconditions,
          nClausesPostconditions,
          nClausesAssertions,
          nClausesLoopInvariants,
          methodMetadata.toMap
        )
      }
    }
    print(
      "Generated " + programPermutations.length + " permutations of the program."
    )
    programPermutations.toList
  }

  def permuteMethods(
      methods: Seq[IRGraph.Method],
      methodExclusionList: Set[String],
      permuteMode: PermuteMode
  ): List[List[PermutedMethod]] = {

    val perMethodPermutations: ListBuffer[List[PermutedMethod]] =
      ListBuffer()

    for (method <- methods) {
      if (!methodExclusionList.contains(method.name)) {
        val permutedPreconditions =
          permuteExpression(method.precondition, permuteMode)
        val permutedPostconditions =
          permuteExpression(method.postcondition, permuteMode)
        val permutedMethodBodies = permuteBlock(method.body, permuteMode)
        println(s"${method.name}: ")
        println(s"  - " + permutedPreconditions.length + " preconditions")
        println(s"  - " + permutedPostconditions.length + " postconditions")
        println(s"  - " + permutedMethodBodies.length + " method bodies")
        println(
          s"  = " + permutedPreconditions.length * permutedPostconditions.length * permutedMethodBodies.length + " total versions"
        )
        var currPermutation = 1
        val methodPermutations = ListBuffer[PermutedMethod]()
        permutedPostconditions.foreach(post => {
          permutedPreconditions.foreach(pre => {
            permutedMethodBodies.foreach(body => {
              val permutation =
                new IRGraph.Method(method.name, method.returnType)
              permutation.precondition = Some(new IRGraph.Imprecise(pre.expr))
              permutation.postcondition = Some(new IRGraph.Imprecise(post.expr))
              permutation.body = new IRGraph.MethodBlock(method)
              permutation.body ++= body.opList.map(op => op.copy)
              methodPermutations += PermutedMethod(
                permutation,
                pre.nClauses,
                post.nClauses,
                body.nClausesAssertions,
                body.nClausesLoopInvariants
              )
              print(
                "\r" + currPermutation + "/" + permutedPreconditions.length * permutedPostconditions.length * permutedMethodBodies.length
              )

              currPermutation += 1
            })
          })
        })
        perMethodPermutations += methodPermutations.toList
      }
    }
    print("\n")
    methods
      .filter(method => methodExclusionList.contains(method.name))
      .foreach(method => perMethodPermutations += List(PermutedMethod(method)))
    crossJoin(perMethodPermutations.toList)
  }

  def permutePredicates(
      predicates: Seq[IRGraph.Predicate],
      permuteMode: PermuteMode
  ): List[List[PermutedPredicate]] = {
    val predicatePermutations = predicates.map(predicate => {
      val permutedPredicateBodies = permuteExpression(
        Some(predicate.expression),
        permuteMode
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

  def appendToAll(
      permutations: List[PermutedBlock],
      op: IRGraph.Op
  ): List[PermutedBlock] = {
    permutations.map(prev =>
      PermutedBlock(
        prev.nClausesAssertions,
        prev.nClausesLoopInvariants,
        prev.opList ++ List(op)
      )
    )
  }

  def permuteToAll(
      permutations: List[PermutedBlock],
      permList: List[PermutedOp]
  ): List[PermutedBlock] = {
    permutations.flatMap(prev => {
      permList.map(curr => {
        PermutedBlock(
          prev.nClausesAssertions + curr.nClausesAssertions,
          prev.nClausesLoopInvariants + curr.nCLausesLoopInvariants,
          if (curr.op.isDefined) prev.opList ++ List(curr.op.get)
          else prev.opList
        )
      })
    })
  }

  def permuteBlock(
      block: IRGraph.Block,
      permuteMode: PermuteMode
  ): List[PermutedBlock] = {
    permuteMode match {
      case gvc.visualizer.PermuteMode.Exp       => permuteBlockExp(block)
      case gvc.visualizer.PermuteMode.Linear    => ???
      case gvc.visualizer.PermuteMode.Field     => ???
      case gvc.visualizer.PermuteMode.Predicate => ???
    }
  }

  def permuteBlockField(block: IRGraph.Block): List[PermutedBlock] = ???
  def permuteBlockPredicate(block: IRGraph.Block): List[PermutedBlock] = ???
  def permuteBlockLinear(block: IRGraph.Block): List[PermutedBlock] = ???

  def permuteBlockExp(
      block: IRGraph.Block
  ): List[PermutedBlock] = {

    var currentPermutations: List[PermutedBlock] = List(
      PermutedBlock(0, 0, List())
    )

    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case fold: IRGraph.Fold =>
          currentPermutations = permuteToAll(
            currentPermutations,
            List(PermutedOp(op = Some(fold)), PermutedOp())
          )
        case unfold: IRGraph.Unfold =>
          currentPermutations = permuteToAll(
            currentPermutations,
            List(PermutedOp(op = Some(unfold)), PermutedOp())
          )
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            currentPermutations = permuteToAll(
              currentPermutations,
              permuteExpressionExp(Some(assert.value)).map(expr => {
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
            currentPermutations = appendToAll(currentPermutations, assert)
          }
        case value: IRGraph.If =>
          val trueBranchPermutations = permuteBlockExp(value.ifTrue)
          val falseBranchPermutations = permuteBlockExp(value.ifFalse)

          currentPermutations = permuteToAll(
            currentPermutations,
            trueBranchPermutations.flatMap(trueBranch => {
              falseBranchPermutations.map(falseBranch => {
                PermutedOp(
                  trueBranch.nClausesAssertions + falseBranch.nClausesAssertions,
                  trueBranch.nClausesLoopInvariants + falseBranch.nClausesLoopInvariants,
                  Some(value.copy(trueBranch.opList, falseBranch.opList))
                )
              })
            })
          )
        case whl: IRGraph.While =>
          val invariantAssertions =
            permuteExpressionExp(whl.invariant)
          val whileBodies = permuteBlockExp(whl.body)
          currentPermutations = permuteToAll(
            currentPermutations,
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
        case other: IRGraph.Op =>
          currentPermutations = appendToAll(currentPermutations, other)
      }
    }
    currentPermutations
  }
  def permuteExpression(
      expression: Option[IRGraph.Expression],
      permuteMode: PermuteMode
  ): List[PermutedExpression] = {

    permuteMode match {
      case gvc.visualizer.PermuteMode.Exp       => permuteExpressionExp(expression)
      case gvc.visualizer.PermuteMode.Linear    => ???
      case gvc.visualizer.PermuteMode.Field     => ???
      case gvc.visualizer.PermuteMode.Predicate => ???
    }
  }
  def permuteExpressionField(block: IRGraph.Block): List[PermutedBlock] = ???
  def permuteExpressionPredicate(block: IRGraph.Block): List[PermutedBlock] =
    ???
  def permuteExpressionLinear(block: IRGraph.Block): List[PermutedBlock] = ???

  def permuteExpressionExp(
      expression: Option[IRGraph.Expression]
  ): List[PermutedExpression] = {
    var permutedClauses = List[PermutedExpression]()
    expression match {
      case Some(expr: IRGraph.Expression) =>
        val numClausesInAssertion = numClauses(expr)
        val conjunctionNodeIndices = permuteIndices(numClausesInAssertion)
        conjunctionNodeIndices.foreach(permutation => {
          val subset =
            extractSubsetOfClauses(permutation, expr)
          permutedClauses =
            PermutedExpression(permutation.length, subset) :: permutedClauses
        })
      case None =>
        permutedClauses = PermutedExpression(0, None) :: permutedClauses
    }
    permutedClauses
  }

  case class ASTMarker(expr: Option[IRGraph.Expression], currentIndex: Int)
  def extractSubsetOfClauses(
      subset: List[Int],
      root: IRGraph.Expression
  ): Option[IRGraph.Expression] = {
    val subsetBuffer = mutable.ListBuffer.empty ++= subset
    extractSubsetOfClauses(subsetBuffer, index = 0, root).expr
  }
  def extractSubsetOfClauses(
      subset: ListBuffer[Int],
      index: Int,
      root: IRGraph.Expression
  ): ASTMarker = {
    if (subset.nonEmpty) {
      root match {
        case binaryRoot: IRGraph.Binary =>
          if (binaryRoot.operator == IRGraph.BinaryOp.And) {
            val rightTraversal =
              extractSubsetOfClauses(subset, index, binaryRoot.right)
            val leftTraversal =
              extractSubsetOfClauses(
                subset,
                rightTraversal.currentIndex,
                binaryRoot.left
              )
            if (rightTraversal.expr.isDefined && leftTraversal.expr.isDefined) {
              ASTMarker(
                Some(
                  new IRGraph.Binary(
                    binaryRoot.operator,
                    leftTraversal.expr.get,
                    rightTraversal.expr.get
                  )
                ),
                leftTraversal.currentIndex
              )
            } else if (rightTraversal.expr.isDefined) {
              ASTMarker(
                rightTraversal.expr,
                leftTraversal.currentIndex
              )
            } else {
              leftTraversal
            }
          } else if (subset.last == index) {
            subset.remove(1, subset.length - 1)
            ASTMarker(Some(binaryRoot), index + 1)
          } else {
            ASTMarker(None, index + 1)
          }

        case cond: IRGraph.Conditional =>
          val ifTrue = extractSubsetOfClauses(subset, index, cond.ifTrue)
          val ifFalse =
            extractSubsetOfClauses(subset, ifTrue.currentIndex, cond.ifFalse)
          ASTMarker(
            Some(
              new IRGraph.Conditional(
                cond.condition,
                new IRGraph.Imprecise(ifTrue.expr),
                new IRGraph.Imprecise(ifFalse.expr)
              )
            ),
            ifFalse.currentIndex
          )
        case _: IRGraph.Expression =>
          if (subset.last == index) {
            ASTMarker(Some(root), index)
          } else {
            ASTMarker(None, index)
          }
      }
    } else {
      ASTMarker(None, index)
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
    expr match {
      case binExp: IRGraph.Binary =>
        if (binExp.operator == IRGraph.BinaryOp.And) {
          numClauses(binExp.right) + numClauses(binExp.left)
        } else {
          1
        }
      case ifExp: IRGraph.Conditional =>
        numClauses(ifExp.ifTrue) + numClauses(ifExp.ifFalse)
      case _ => 1
    }
  }
}
