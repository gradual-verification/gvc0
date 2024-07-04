package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR
import viper.silver.{ast => vpr}

object Collector {
  class CollectedChecks(val method: IR.Method) {
    val conditions = mutable.HashSet[TrackedCondition]()
    val checks = mutable.ListBuffer[RuntimeCheck]()
  }

  class CollectedProgram(
      val program: IR.Program,
      val methods: Map[String, CollectedChecks]
  )

  def collect(
      irProgram: IR.Program,
      vprProgram: vpr.Program
  ): CollectedProgram = {
    val checks = ViperChecks.collect(vprProgram)

    val methods = irProgram.methods
      .map(
        m =>
          (
            m.name,
            collect(
              irProgram,
              vprProgram,
              m,
              vprProgram.findMethod(m.name),
              checks
            )
        ))
      .toMap

    new CollectedProgram(
      program = irProgram,
      methods = methods
    )
  }

  private def unwrap(expr: CheckExpression,
                     value: Boolean = true): (CheckExpression, Boolean) = {
    expr match {
      case CheckExpression.Not(operand) => unwrap(operand, !value)
      case e                            => (e, value)
    }
  }

  private def collect(
      irProgram: IR.Program,
      vprProgram: vpr.Program,
      irMethod: IR.Method,
      vprMethod: vpr.Method,
      vprChecks: ViperChecks.CheckMap
  ): CollectedChecks = {
    // A mapping of Viper node IDs to the corresponding IR op.
    // This is used for locating the correct insertion of conditionals.
    val locations = mutable.Map[Int, Location]()

    val collected = new CollectedChecks(irMethod)

    val separationLocations = mutable.HashSet[Location]()

    // Indexing adds the node to the mapping of Viper locations to IR locations
    def index(node: vpr.Node, location: Location): Unit =
      locations += node.uniqueIdentifier -> location

    // Indexes the given node and all of its child nodes
    def indexAll(node: vpr.Node, loc: Location): Unit =
      node.visit { case n => locations += n.uniqueIdentifier -> loc }

    // Finds all the runtime checks required by the given Viper node, and adds them at the given
    // IR location.
    // `loopInvs` is the list of the invariants from all the loops that contain this position.
    def check(
        node: vpr.Node,
        loc: Location,
        methodCall: Option[vpr.Method],
        loopInvs: List[vpr.Exp]
    ): Unit = {
      vprChecks.get(node.uniqueIdentifier) match {
        case None => ()
        case Some(checks) =>
          for (c <- checks)
            collected.checks += convertCheck(c, node, loc, methodCall, loopInvs)
      }
    }

    def convertCheck(
      vprCheck: ViperCheck,
      node: vpr.Node,
      loc: Location,
      methodCall: Option[vpr.Method],
      loopInvs: List[vpr.Exp]
    ): RuntimeCheck = {
      val (checkLocation, inSpec) = loc match {
          case at: AtOp =>
            vprCheck.location match {
              case ViperLocation.Value =>
                methodCall match {
                  case Some(method) =>
                    if (ViperChecks.isContained(vprCheck.context, method.posts))
                      (Post(at.op), true)
                    else if (ViperChecks.isContained(vprCheck.context, method.pres))
                      (Pre(at.op), true)
                    else
                      (Pre(at.op), false)
                  case _ => (Pre(at.op), false)
                }
              case ViperLocation.PreLoop | ViperLocation.PreInvoke |
                  ViperLocation.Fold | ViperLocation.Unfold =>
                (Pre(at.op), true)
              case ViperLocation.PostLoop | ViperLocation.PostInvoke =>
                (Post(at.op), true)
              case ViperLocation.InvariantLoopStart =>
                (LoopStart(at.op), true)
              case ViperLocation.InvariantLoopEnd =>
                (LoopEnd(at.op), true)
            }
          case _ => {
            if (vprCheck.location != ViperLocation.Value)
              throw new WeaverException("Invalid check location")
            (loc, loc == MethodPre || loc == MethodPost)
          }
        }

        val check = Check.fromViper(vprCheck.check)
        if (inSpec) {
          check match {
            case _: AccessibilityCheck => separationLocations += loc
            case _ => ()
          }
        }

        RuntimeCheck(
          loc,
          check,
          branchCondition(checkLocation, vprCheck.conditions, loopInvs)
        )
    }


    // Recursively collects all runtime checks
    def checkAll(
        node: vpr.Node,
        loc: Location,
        methodCall: Option[vpr.Method],
        loopInvs: List[vpr.Exp]
    ): Unit =
      node.visit { case n => check(n, loc, methodCall, loopInvs) }

    // Combines indexing and runtime check collection for a given Viper node. Indexing must be
    // completed first, since the conditions on a runtime check may be at locations contained in
    // the same node.
    def visit(op: IR.Op, node: vpr.Node, loopInvs: List[vpr.Exp]): Unit = {
      val loc = Pre(op)
      node match {
        case iff: vpr.If => {
          index(iff, loc)
          indexAll(iff.cond, loc)

          check(iff, loc, None, loopInvs)
          checkAll(iff.cond, loc, None, loopInvs)
        }

        case call: vpr.MethodCall => {
          val method = vprProgram.findMethod(call.methodName)
          indexAll(call, loc)
          checkAll(call, loc, Some(method), loopInvs)
        }

        case loop: vpr.While => {
          index(loop, loc)
          indexAll(loop.cond, loc)
          loop.invs.foreach(indexAll(_, loc))

          check(loop, loc, None, loopInvs)
          checkAll(loop.cond, loc, None, loopInvs)

          // Invariants are checked after loop body
        }

        case n => {
          indexAll(n, loc)
          checkAll(n, loc, None, loopInvs)
        }
      }
    }

    def visitBlock(
        irBlock: IR.Block,
        vprBlock: vpr.Seqn,
        loopInvs: List[vpr.Exp]
    ): Unit = {
      var vprOps = vprBlock.ss.toList
      for (irOp <- irBlock) {
        vprOps = (irOp, vprOps) match {
          case (irIf: IR.If, (vprIf: vpr.If) :: vprRest) => {
            visit(irIf, vprIf, loopInvs)
            visitBlock(irIf.ifTrue, vprIf.thn, loopInvs)
            visitBlock(irIf.ifFalse, vprIf.els, loopInvs)
            vprRest
          }
          case (irWhile: IR.While, (vprWhile: vpr.While) :: vprRest) => {
            visit(irWhile, vprWhile, loopInvs)
            // Supports only a single invariant
            val newInvs =
              vprWhile.invs.headOption.map(_ :: loopInvs).getOrElse(loopInvs)
            visitBlock(irWhile.body, vprWhile.body, newInvs)

            // Check invariants after loop body since they may depend on conditions from body
            vprWhile.invs.foreach { i =>
              checkAll(i, Pre(irWhile), None, loopInvs)
            }

            vprRest
          }
          case (irInvoke: IR.Invoke, (vprInvoke: vpr.MethodCall) :: vprRest) => {
            visit(irInvoke, vprInvoke, loopInvs)
            vprRest
          }
          case (irAlloc: IR.AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            visit(irAlloc, vprAlloc, loopInvs)
            vprRest
          }
          case (irAlloc: IR.AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            visit(irAlloc, vprAlloc, loopInvs)
            vprRest
          }
          case (
              irAssign: IR.Assign,
              (vprAssign: vpr.LocalVarAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign, loopInvs)
            vprRest
          }
          case (
              irAssign: IR.AssignMember,
              (vprAssign: vpr.FieldAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign, loopInvs)
            vprRest
          }
          case (irAssert: IR.Assert, vprRest)
              if irAssert.kind == IR.AssertKind.Imperative =>
            vprRest
          case (irAssert: IR.Assert, (vprAssert: vpr.Assert) :: vprRest)
              if irAssert.kind == IR.AssertKind.Specification => {
            visit(irAssert, vprAssert, loopInvs)
            vprRest
          }
          case (irFold: IR.Fold, (vprFold: vpr.Fold) :: vprRest) => {
            visit(irFold, vprFold, loopInvs)
            vprRest
          }
          case (irUnfold: IR.Unfold, (vprUnfold: vpr.Unfold) :: vprRest) => {
            visit(irUnfold, vprUnfold, loopInvs)
            vprRest
          }
          case (irError: IR.Error, (vprError: vpr.Assert) :: vprRest) => {
            visit(irError, vprError, loopInvs)
            vprRest
          }
          case (irReturn: IR.Return, vprRest) if irReturn.value.isEmpty => {
            vprRest
          }
          case (irReturn: IR.Return, (vprReturn: vpr.LocalVarAssign) :: vprRest)
              if irReturn.value.isDefined => {
            visit(irReturn, vprReturn, loopInvs)
            vprRest
          }

          // Errors
          case (ir, vprStmt :: _) =>
            throw new WeaverException(
              s"Unexpected Silver statement: $vprStmt for $ir"
            )
          case (_, Nil) =>
            throw new WeaverException("Expected Silver statement")
        }
      }

      if (vprOps.nonEmpty) {
        throw new WeaverException(
          s"Unexpected Silver statement: ${vprOps.head}"
        )
      }
    }

    def normalizeLocation(loc: Location): Location = loc match {
      // Pre of first op in the method is the same as MethodPre
      case Pre(op) if (op.getPrev.isEmpty && op.block == irMethod.body) =>
        MethodPre

      // Post is the same as Pre of the next op
      case Post(op) if (op.getNext.isDefined) => Pre(op.getNext.get)

      // LoopStart is the same as Pre of the first op in the loop
      case LoopStart(op: IR.While) if op.body.nonEmpty => Pre(op.body.head)

      // LoopEnd is the same as Post of the last op in the loop
      case LoopEnd(op: IR.While) if op.body.nonEmpty => Post(op.body.last)

      // Otherwise, don't change
      case loc => loc
    }

    // Converts the stack of branch conditions from the verifier to a logical conjunction
    def branchCondition(
        location: Location,
        branches: List[ViperBranch],
        loopInvs: List[vpr.Exp]
    ): Option[Condition] = {
      branches.foldRight[Option[Condition]](None)((b, when) => {
        val irLoc = locations.getOrElse(
          b.at.uniqueIdentifier,
          throw new WeaverException(
            s"Could not find location for ${b.at}"
          )
        )

        val position = b.location match {
          // Special case for when the verifier uses positions tagged as the beginning of the loop
          // outside of the loop body. In this case, just use the after loop position.
          case ViperLocation.InvariantLoopStart
              if !ViperChecks.isContained(b.at, loopInvs) =>
            ViperLocation.PostLoop
          case p => p
        }

        val conditionLocation =
          normalizeLocation(ViperLocation.forIR(irLoc, position))
        val (expr, flag) =
          unwrap(CheckExpression.fromViper(b.condition))

        val unwrappedCondition: Condition =
          if (conditionLocation == normalizeLocation(location)) {
            ImmediateCondition(expr)
          } else {
            val cond = TrackedCondition(conditionLocation, expr.guarded)
            collected.conditions += cond
            cond
          }

        val cond =
          if (flag) unwrappedCondition else NotCondition(unwrappedCondition)

        Some(when match {
          case None                       => cond
          case Some(AndCondition(values)) => AndCondition(values :+ cond)
          case Some(other)                => AndCondition(List(other, cond))
        })
      })
    }

    // Index pre-conditions and add required runtime checks
    vprMethod.pres.foreach(indexAll(_, MethodPre))
    vprMethod.pres.foreach(checkAll(_, MethodPre, None, Nil))

    // Loop through each operation and collect checks
    visitBlock(irMethod.body, vprMethod.body.get, Nil)

    // Index post-conditions and add required runtime checks
    vprMethod.posts.foreach(indexAll(_, MethodPost))
    vprMethod.posts.foreach(checkAll(_, MethodPost, None, Nil))

    // Add separation checks
    SeparationChecks.inject(separationLocations, irMethod, collected.checks)

    collected
  }
  
}
