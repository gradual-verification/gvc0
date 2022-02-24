package gvc.visualizer
import gvc.Main.generateIR
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.visualizer.PermuteMode.PermuteMode
import gvc.visualizer.PermuteTarget.PermuteTarget

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

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
      permuteModes: Map[PermuteTarget, PermuteMode]
  ): List[ProgramPermutation] = {
    val program = generateIR(c0Source)
    val programPermutations: ListBuffer[ProgramPermutation] = ListBuffer()

    val methodPermutations: List[List[PermutedMethod]] = permuteMethods(
      program.methods,
      methodExclusionList,
      permuteModes
    )
    val predicatePermutations: List[List[PermutedPredicate]] =
      permutePredicates(
        program.predicates,
        permuteModes
      )

    val totalPrograms = methodPermutations.length * predicatePermutations.length
    var currProgram = 1

    print("Printing permutations...")
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
        print(
          "\r" + currProgram + "/" + totalPrograms
        )
        currProgram += 1

      }
    }

    println(
      "\nGenerated " + programPermutations.length + " permutations of the program."
    )
    programPermutations.toList
  }

  def permuteMethods(
      methods: Seq[IRGraph.Method],
      methodExclusionList: Set[String],
      permuteModes: Map[PermuteTarget, PermuteMode]
  ): List[List[PermutedMethod]] = {

    val perMethodPermutations: ListBuffer[List[PermutedMethod]] =
      ListBuffer()

    for (method <- methods) {
      if (!methodExclusionList.contains(method.name)) {
        val permutedPreconditions =
          permuteExpression(method.precondition, permuteModes)
        val permutedPostconditions =
          permuteExpression(method.postcondition, permuteModes)
        val permutedMethodBodies = permuteBlock(method.body, permuteModes)
        println(s"METHOD: ${method.name}: ")
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
                "\r   -> Generated " + currPermutation + "/" + permutedPreconditions.length * permutedPostconditions.length * permutedMethodBodies.length
              )

              currPermutation += 1
            })
          })
        })
        perMethodPermutations += methodPermutations.toList
        print("\n")

      }
    }
    methods
      .filter(method => methodExclusionList.contains(method.name))
      .foreach(method => perMethodPermutations += List(PermutedMethod(method)))
    crossJoin(perMethodPermutations.toList)
  }

  def permutePredicates(
      predicates: Seq[IRGraph.Predicate],
      permuteModes: Map[PermuteTarget, PermuteMode]
  ): List[List[PermutedPredicate]] = {
    var currPermutation = 1;
    val predicatePermutations = predicates.map(predicate => {
      println(s"PREDICATE: ${predicate.name}: ")
      val permutedPredicateBodies = permuteExpression(
        Some(predicate.expression),
        permuteModes
      )
      println(s"  - " + permutedPredicateBodies.length + " bodies")
      permutedPredicateBodies.map(body => {
        print(
          "\r   -> Generated " + currPermutation + "/" + permutedPredicateBodies.length
        )
        currPermutation += 1
        PermutedPredicate(
          predicate.copy(new IRGraph.Imprecise(body.expr)),
          body.nClauses
        )
      })
    })
    print("\n")
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

  def permuteBlock(
      block: IRGraph.Block,
      permuteModes: Map[PermuteTarget, PermuteMode]
  ): List[PermutedBlock] = {
    val permuter = new BlockPermuter()
    val it = block.iterator
    while (it.hasNext) {
      val op = it.next()
      op match {
        case fold: IRGraph.Fold =>
          permuter.permute(
            PermutedOp(op = Some(fold)),
            permuteModes
          )
        case unfold: IRGraph.Unfold =>
          permuter.permute(
            PermutedOp(op = Some(unfold)),
            permuteModes
          )
        case assert: IRGraph.Assert =>
          if (assert.kind == IRGraph.AssertKind.Specification) {
            permuter.permute(
              permuteExpression(Some(assert.value), permuteModes).map(expr => {
                PermutedOp(
                  nClausesAssertions = expr.nClauses,
                  op = Some(
                    new IRGraph.Assert(
                      new IRGraph.Imprecise(expr.expr),
                      IRGraph.AssertKind.Specification
                    )
                  )
                )
              }),
              permuteModes
            )
          } else {
            permuter.permute(
              PermutedOp(op = Some(assert)),
              permuteModes
            )
          }
        case value: IRGraph.If =>
          val trueBranchPermutations =
            permuteBlock(value.ifTrue, permuteModes)
          val falseBranchPermutations =
            permuteBlock(value.ifFalse, permuteModes)
          trueBranchPermutations.flatMap(trueBranch => {
            falseBranchPermutations.map(falseBranch => {
              permuter.permute(
                PermutedOp(
                  trueBranch.nClausesAssertions + falseBranch.nClausesAssertions,
                  trueBranch.nClausesLoopInvariants + falseBranch.nClausesLoopInvariants,
                  Some(value.copy(trueBranch.opList, falseBranch.opList))
                ),
                permuteModes
              )
            })
          })
        case whl: IRGraph.While =>
          val invariantAssertions =
            permuteExpression(whl.invariant, permuteModes)
          val whileBodies = permuteBlock(whl.body, permuteModes)
          invariantAssertions.flatMap(invAssert => {
            whileBodies.map(body => {
              permuter.permute(
                PermutedOp(
                  body.nClausesAssertions,
                  body.nClausesLoopInvariants + invAssert.nClauses,
                  Some(whl.copy(invAssert.expr, body.opList))
                ),
                permuteModes
              )
            })
          })
        case other: IRGraph.Op =>
          permuter.permute(
            PermutedOp(op = Some(other)),
            permuteModes
          )
      }
    }
    permuter.gather()
  }

  def permuteExpression(
      rootOption: Option[IRGraph.Expression],
      permuteModes: Map[PermuteTarget, PermuteMode]
  ): List[PermutedExpression] = {
    rootOption match {
      case Some(root) =>
        val expPermuter = new ExpressionPermuter()
        val expStack = ListBuffer[IRGraph.Expression](root)
        while (expStack.nonEmpty) {
          val top = expStack.remove(expStack.length - 1)
          top match {
            case conditional: IRGraph.Conditional =>
              val trueBranches =
                permuteExpression(Some(conditional.ifTrue), permuteModes)
              val falseBranches =
                permuteExpression(Some(conditional.ifFalse), permuteModes)
              trueBranches.map(tBranch => {
                falseBranches.map(fBranch => {
                  val tExpr =
                    if (tBranch.expr.isDefined) tBranch.expr.get
                    else new IRGraph.Bool(value = true)
                  val fExpr =
                    if (fBranch.expr.isDefined) fBranch.expr.get
                    else new IRGraph.Bool(value = true)
                  val permutedIf = new IRGraph.Conditional(
                    conditional.condition,
                    tExpr,
                    fExpr
                  )
                  expPermuter.permute(
                    PermutedExpression(
                      tBranch.nClauses + fBranch.nClauses,
                      Some(
                        permutedIf
                      )
                    ),
                    permuteModes
                  )
                })
              })
            case binary: IRGraph.Binary =>
              if (binary.operator == IRGraph.BinaryOp.And) {
                expStack += binary.left
                expStack += binary.right
              } else {
                expPermuter.permute(
                  PermutedExpression(1, Some(binary)),
                  permuteModes
                )
              }
            case expr: IRGraph.Expression =>
              expPermuter.permute(
                PermutedExpression(1, Some(expr)),
                permuteModes
              )
          }
        }
        expPermuter.gather()
      case None => List(PermutedExpression(0, None))
    }
  }
}
