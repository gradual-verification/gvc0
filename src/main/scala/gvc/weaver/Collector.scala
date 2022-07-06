package gvc.weaver

import gvc.transformer.IR.Predicate

import scala.collection.mutable
import gvc.transformer.{IR, SilverProgram, SilverVarId}
import viper.silver.ast.MethodCall
import viper.silver.{ast => vpr}
import viper.silicon.state.CheckPosition
import viper.silicon.state.LoopPosition
import viper.silicon.state.BranchCond

object Collector {
  sealed trait Location

  sealed trait AtOp extends Location {
    val op: IR.Op
  }

  case class Pre(override val op: IR.Op) extends AtOp

  case class Post(override val op: IR.Op) extends AtOp

  case class LoopStart(override val op: IR.Op) extends AtOp

  case class LoopEnd(override val op: IR.Op) extends AtOp

  case object MethodPre extends Location

  case object MethodPost extends Location

  sealed trait Condition

  case class NotCondition(value: Condition) extends Condition

  case class AndCondition(values: List[Condition]) extends Condition

  case class OrCondition(values: List[Condition]) extends Condition

  case class ImmediateCondition(value: CheckExpression) extends Condition

  case class TrackedCondition(
      location: Location,
      value: CheckExpression
  ) extends Condition

  case class CheckInfo(
      check: Check,
      when: Option[Condition]
  )

  case class RuntimeCheck(
      location: Location,
      check: Check,
      when: Option[Condition]
  )

  sealed trait CallStyle

  case object PreciseCallStyle extends CallStyle

  case object PrecisePreCallStyle extends CallStyle

  case object ImpreciseCallStyle extends CallStyle

  case object MainCallStyle extends CallStyle

  class CollectedMethod(
      val method: IR.Method,
      val conditions: List[TrackedCondition],
      val checks: List[RuntimeCheck],
      val returns: List[IR.Return],
      val hasImplicitReturn: Boolean,
      val calls: List[CollectedInvocation],
      val allocations: List[IR.Op],
      val callStyle: CallStyle,
      val bodyContainsImprecision: Boolean,
      val checkedSpecificationLocations: Set[Location]
  )

  class CollectedProgram(
      val program: IR.Program,
      val temporaryVars: Map[SilverVarId, IR.Invoke],
      val methods: Map[String, CollectedMethod],
      val imprecisionPresent: Boolean,
      val requiresFieldAccessCheck: Boolean,
  )

  case class CollectedInvocation(ir: IR.Invoke, vpr: MethodCall)

  def collect(
      irProgram: IR.Program,
      vprProgram: SilverProgram
  ): CollectedProgram = {
    val checks = collectChecks(vprProgram.program)

    val methods = irProgram.methods
      .map(
        m =>
          (
            m.name,
            collect(
              irProgram,
              vprProgram.program,
              m,
              vprProgram.program.findMethod(m.name),
              checks
            )
        ))
      .toMap

    val imprecisionPresent = methods.exists(m => {
      m._2.bodyContainsImprecision || m._2.callStyle != PreciseCallStyle && m._2.callStyle != MainCallStyle
    })

    val requiresFieldAccessCheck = methods.exists(m =>
      m._2.checks.exists(p => {
        p.check.isInstanceOf[PermissionCheck]
      }))
    new CollectedProgram(
      program = irProgram,
      temporaryVars = vprProgram.temporaryVars,
      methods = methods,
      imprecisionPresent,
      requiresFieldAccessCheck
    )
  }

  private class ConditionTerm(val id: Int) {
    val conditions = mutable.Set[Logic.Conjunction]()
  }

  private sealed trait ViperLocation

  private object ViperLocation {
    case object Value extends ViperLocation

    case object PreInvoke extends ViperLocation

    case object PostInvoke extends ViperLocation

    case object PreLoop extends ViperLocation

    case object PostLoop extends ViperLocation

    case object Fold extends ViperLocation

    case object Unfold extends ViperLocation

    case object InvariantLoopStart extends ViperLocation

    case object InvariantLoopEnd extends ViperLocation

    def loop(loopPosition: LoopPosition): ViperLocation = loopPosition match {
      case LoopPosition.After     => ViperLocation.PreLoop
      case LoopPosition.Before    => ViperLocation.PostLoop
      case LoopPosition.Beginning => ViperLocation.InvariantLoopStart
      case LoopPosition.End       => ViperLocation.InvariantLoopEnd
    }

    def forIR(irLocation: Location, vprLocation: ViperLocation): Location =
      irLocation match {
        case at: AtOp =>
          vprLocation match {
            case ViperLocation.PreInvoke | ViperLocation.PreLoop |
                ViperLocation.Fold | ViperLocation.Unfold |
                ViperLocation.Value =>
              Pre(at.op)
            case ViperLocation.PostInvoke | ViperLocation.PostLoop =>
              Post(at.op)
            case ViperLocation.InvariantLoopStart => LoopStart(at.op)
            case ViperLocation.InvariantLoopEnd   => LoopEnd(at.op)
          }
        case _ => {
          if (vprLocation != ViperLocation.Value)
            throw new WeaverException("Invalid location")
          irLocation
        }
      }
  }

  private case class ViperBranch(
      at: vpr.Node,
      location: ViperLocation,
      condition: vpr.Exp
  )

  private object ViperBranch {
    def apply(
        branch: BranchCond,
        program: vpr.Program
    ) = branch match {
      case BranchCond(
          condition,
          position,
          Some(CheckPosition.GenericNode(invoke: vpr.MethodCall))
          ) => {
        // This must be a method pre-condition or post-condition
        val callee = program.findMethod(invoke.methodName)

        val location: ViperLocation =
          if (isContained(position, callee.posts)) ViperLocation.PostInvoke
          else if (isContained(position, callee.pres)) ViperLocation.PreInvoke
          else ViperLocation.Value
        new ViperBranch(invoke, location, condition)
      }

      case BranchCond(
          condition,
          position,
          Some(CheckPosition.GenericNode(unfold: vpr.Unfold))
          ) =>
        new ViperBranch(unfold, ViperLocation.Fold, condition)
      case BranchCond(
          condition,
          position,
          Some(CheckPosition.GenericNode(unfold: vpr.Fold))
          ) =>
        new ViperBranch(unfold, ViperLocation.Unfold, condition)

      case BranchCond(
          condition,
          _,
          Some(CheckPosition.Loop(inv, position))
          ) => {
        // This must be an invariant
        if (inv.isEmpty || !inv.tail.isEmpty)
          throw new WeaverException("Invalid loop invariant")

        new ViperBranch(inv.head, ViperLocation.loop(position), condition)
      }

      case BranchCond(condition, position, None) => {
        new ViperBranch(position, ViperLocation.Value, condition)
      }

      case _ => throw new WeaverException("Invalid branch condition")
    }
  }

  private case class ViperCheck(
      check: vpr.Exp,
      conditions: List[ViperBranch],
      location: ViperLocation,
      context: vpr.Exp
  )

  private type ViperCheckMap =
    mutable.HashMap[Int, mutable.ListBuffer[ViperCheck]]

  // Convert the verifier's check map into a ViperCheckMap
  private def collectChecks(vprProgram: vpr.Program): ViperCheckMap = {
    val vprChecks = viper.silicon.state.runtimeChecks.getChecks
    val collected = new ViperCheckMap()

    for ((pos, checks) <- vprChecks) {
      val (node, location) = pos match {
        case CheckPosition.GenericNode(node) => (node, ViperLocation.Value)
        case CheckPosition.Loop(invariants, position) => {
          if (invariants.tail.nonEmpty)
            throw new WeaverException("Invalid loop invariant")
          (invariants.head, ViperLocation.loop(position))
        }
      }

      val list =
        collected.getOrElseUpdate(node.uniqueIdentifier, mutable.ListBuffer())
      for (c <- checks) {
        val conditions = c.branchInfo.map(ViperBranch(_, vprProgram)).toList
        list += ViperCheck(c.checks, conditions, location, c.context)
      }
    }

    collected
  }

  private def isContained(node: vpr.Node, container: vpr.Node): Boolean = {
    container.visit {
      case n => {
        if (n.uniqueIdentifier == node.uniqueIdentifier) {
          return true
        }
      }
    }

    false
  }

  private def isContained(node: vpr.Node, containers: Seq[vpr.Node]): Boolean =
    containers.exists(isContained(node, _))

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
      vprChecks: ViperCheckMap
  ): CollectedMethod = {
    // A mapping of Viper node IDs to the corresponding IR op.
    // This is used for locating the correct insertion of conditionals.
    val locations = mutable.Map[Int, Location]()

    // A list of `return` statements in the IR method, used for inserting any runtime checks that
    // the postcondition may require.
    val exits = mutable.ListBuffer[IR.Return]()
    // A list of invocations and allocations, used for inserting permission tracking
    val invokes = mutable.ListBuffer[CollectedInvocation]()
    val allocations = mutable.ListBuffer[IR.Op]()

    // The collection of conditions that are used in runtime checks
    val trackedConditions = mutable.LinkedHashSet[TrackedCondition]()

    // The collection of runtime checks that are required, mapping a runtime check to the list of
    // conjuncts where one conjunct must be true in order for the runtime check to occur.
    // Note: Uses a List as a Map so that the order is preserved in the way that the verifier
    // determines (this is important for acc checks of a nested field, for example).
    val checks =
      mutable.Map[Location,
                  mutable.ListBuffer[
                    (Check, mutable.ListBuffer[Option[Condition]])
                  ]]()

    // A set of all locations that need the full specification walked to verify separation. Used
    // to implement the semantics of the separating conjunction. Pre-calculates a set so that the
    // same location is not checked twice.
    val needsFullPermissionChecking = mutable.Set[Location]()

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
      for (vprCheck <- vprChecks.get(node.uniqueIdentifier).toSeq.flatten) {
        val (checkLocation, inSpec) = loc match {
          case at: AtOp =>
            vprCheck.location match {
              case ViperLocation.Value =>
                methodCall match {
                  case Some(method) =>
                    if (isContained(vprCheck.context, method.posts))
                      (Post(at.op), true)
                    else if (isContained(vprCheck.context, method.pres))
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

        val condition =
          branchCondition(checkLocation, vprCheck.conditions, loopInvs)

        // TODO: Split apart ANDed checks?
        val check = Check.fromViper(vprCheck.check, irProgram, irMethod)

        val locationChecks =
          checks.getOrElseUpdate(checkLocation, mutable.ListBuffer())
        val conditions = locationChecks.find {
          case (c, _) =>
            c == check
        } match {
          case Some((_, conditions)) => conditions
          case None =>
            val conditions = mutable.ListBuffer[Option[Condition]]()
            locationChecks += (check -> conditions)
            conditions
        }

        conditions += condition

        if (check.isInstanceOf[
              AccessibilityCheck
            ] && inSpec) {
          needsFullPermissionChecking += checkLocation
        }
      }
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
    ): Boolean = {
      var containsImprecision = false
      var vprOps = vprBlock.ss.toList
      for (irOp <- irBlock) {
        vprOps = (irOp, vprOps) match {
          case (irIf: IR.If, (vprIf: vpr.If) :: vprRest) => {
            visit(irIf, vprIf, loopInvs)
            containsImprecision = visitBlock(irIf.ifTrue, vprIf.thn, loopInvs) || containsImprecision
            containsImprecision = visitBlock(irIf.ifFalse, vprIf.els, loopInvs) || containsImprecision
            vprRest
          }
          case (irWhile: IR.While, (vprWhile: vpr.While) :: vprRest) => {
            visit(irWhile, vprWhile, loopInvs)
            // Supports only a single invariant
            containsImprecision = containsImprecision || isImprecise(
              Some(irWhile.invariant))
            val newInvs =
              vprWhile.invs.headOption.map(_ :: loopInvs).getOrElse(loopInvs)
            containsImprecision = visitBlock(irWhile.body,
                                             vprWhile.body,
                                             newInvs) || containsImprecision

            // Check invariants after loop body since they may depend on conditions from body
            vprWhile.invs.foreach { i =>
              checkAll(i, Pre(irWhile), None, loopInvs)
            }

            vprRest
          }
          case (irInvoke: IR.Invoke, (vprInvoke: vpr.MethodCall) :: vprRest) => {
            invokes += CollectedInvocation(irInvoke, vprInvoke)
            visit(irInvoke, vprInvoke, loopInvs)
            vprRest
          }
          case (irAlloc: IR.AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
            visit(irAlloc, vprAlloc, loopInvs)
            vprRest
          }
          case (irAlloc: IR.AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
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
            containsImprecision = containsImprecision || isImprecise(
              Some(irFold.instance.predicate.expression),
              mutable.Set(irFold.instance.predicate))
            visit(irFold, vprFold, loopInvs)
            vprRest
          }
          case (irUnfold: IR.Unfold, (vprUnfold: vpr.Unfold) :: vprRest) => {
            containsImprecision = containsImprecision || isImprecise(
              Some(irUnfold.instance.predicate.expression),
              mutable.Set(irUnfold.instance.predicate))
            visit(irUnfold, vprUnfold, loopInvs)
            vprRest
          }
          case (irError: IR.Error, (vprError: vpr.Assert) :: vprRest) => {
            visit(irError, vprError, loopInvs)
            vprRest
          }
          case (irReturn: IR.Return, vprRest) if irReturn.value.isEmpty => {
            exits += irReturn
            vprRest
          }
          case (irReturn: IR.Return, (vprReturn: vpr.LocalVarAssign) :: vprRest)
              if irReturn.value.isDefined => {
            visit(irReturn, vprReturn, loopInvs)
            exits += irReturn
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
      containsImprecision
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
              if !isContained(b.at, loopInvs) =>
            ViperLocation.PostLoop
          case p => p
        }

        val conditionLocation =
          normalizeLocation(ViperLocation.forIR(irLoc, position))
        val (expr, flag) =
          unwrap(CheckExpression.fromViper(b.condition, irMethod))

        val unwrappedCondition: Condition =
          if (conditionLocation == normalizeLocation(location)) {
            ImmediateCondition(expr)
          } else {
            val tracked = TrackedCondition(conditionLocation, expr.guarded)
            trackedConditions += tracked
            tracked
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
    val bodyContainsImprecision =
      visitBlock(irMethod.body, vprMethod.body.get, Nil)

    // Index post-conditions and add required runtime checks
    vprMethod.posts.foreach(indexAll(_, MethodPost))
    vprMethod.posts.foreach(checkAll(_, MethodPost, None, Nil))

    // Check if execution can fall-through to the end of the method
    // It is valid to only check the last operation since we don't allow early returns
    val implicitReturn: Boolean = hasImplicitReturn(irMethod)

    // Get all checks (grouped by their location) and simplify their conditions
    val collectedChecks = mutable.ListBuffer[RuntimeCheck]()
    for ((loc, locChecks) <- checks)
      for ((check, conditions) <- locChecks) {
        val condition =
          if (conditions.isEmpty || conditions.contains(None)) {
            None
          } else if (conditions.size == 1) {
            conditions.head
          } else {
            Some(OrCondition(conditions.map(_.get).toList))
          }

        collectedChecks += RuntimeCheck(loc, check, condition)
      }

    // Traverse the specifications for statements that require full permission checks
    for (location <- needsFullPermissionChecking) {
      val (spec, arguments) = location match {
        case at: AtOp =>
          at.op match {
            case op: IR.Invoke =>
              op.callee match {
                case callee: IR.Method if callee.precondition.isDefined =>
                  (
                    callee.precondition.get,
                    Some(
                      op.callee.parameters
                        .zip(op.arguments.map(resolveValue(_)))
                        .toMap
                    )
                  )
                case _ =>
                  throw new WeaverException(
                    s"Could not locate specification at invoke: $location")
              }
            // TODO: Do we need unfold?
            case op: IR.Fold =>
              (
                op.instance.predicate.expression,
                Some(
                  op.instance.predicate.parameters
                    .zip(op.instance.arguments.map(resolveValue(_)))
                    .toMap
                )
              )
            case op: IR.While  => (op.invariant, None)
            case op: IR.Assert => (op.value, None)
            case _ =>
              throw new WeaverException(
                "Could not locate specification for permission checking: " + location
                  .toString()
              )
          }
        case MethodPost if irMethod.postcondition.isDefined =>
          (irMethod.postcondition.get, None)
        case _ =>
          throw new WeaverException(
            "Could not locate specification for permission checking: " + location
              .toString()
          )
      }

      val separationChecks =
        traversePermissions(spec, arguments, None, Separation).map(info =>
          RuntimeCheck(location, info.check, info.when))

      // Since the checks are for separation, only include them if there is more than one
      // otherwise, there can be no overlap
      val needsSeparationCheck =
        separationChecks.length > 1 ||
          separationChecks.length == 1 && !separationChecks.head.check
            .isInstanceOf[FieldSeparationCheck]
      if (needsSeparationCheck) {
        collectedChecks ++= separationChecks
      }
    }

    // Wrap up all the results
    new CollectedMethod(
      method = irMethod,
      conditions = trackedConditions.toList,
      checks = collectedChecks.toList,
      returns = exits.toList,
      hasImplicitReturn = implicitReturn,
      calls = invokes.toList,
      allocations = allocations.toList,
      callStyle = getCallstyle(irMethod),
      bodyContainsImprecision = bodyContainsImprecision,
      checkedSpecificationLocations = needsFullPermissionChecking.toSet
    )
  }

  // TODO: Factor this out
  def traversePermissions(
      spec: IR.Expression,
      arguments: Option[Map[IR.Parameter, CheckExpression]],
      condition: Option[CheckExpression],
      checkType: CheckType
  ): Seq[CheckInfo] = spec match {
    // Imprecise expressions just needs the precise part checked.
    // TODO: This should also enable framing checks.
    case imp: IR.Imprecise => {
      imp.precise.toSeq.flatMap(
        traversePermissions(_, arguments, condition, checkType)
      )
    }

    // And expressions just traverses both parts
    case and: IR.Binary if and.operator == IR.BinaryOp.And => {
      val left = traversePermissions(and.left, arguments, condition, checkType)
      val right =
        traversePermissions(and.right, arguments, condition, checkType)
      left ++ right
    }

    // A condition expression traverses each side with its respective condition, joined with the
    // existing condition if provided to support nested conditionals.
    case cond: IR.Conditional => {
      val baseCond = resolveValue(cond.condition, arguments)
      val negCond = CheckExpression.Not(baseCond)
      val (trueCond, falseCond) = condition match {
        case None => (baseCond, negCond)
        case Some(otherCond) =>
          (
            CheckExpression.And(otherCond, baseCond),
            CheckExpression.And(otherCond, negCond)
          )
      }

      val truePerms =
        traversePermissions(cond.ifTrue, arguments, Some(trueCond), checkType)
      val falsePerms = traversePermissions(
        cond.ifFalse,
        arguments,
        Some(falseCond),
        checkType
      )
      truePerms ++ falsePerms
    }

    // A single accessibility check
    case acc: IR.Accessibility => {
      val field = resolveValue(acc.member, arguments) match {
        case f: CheckExpression.Field => f
        case invalid =>
          throw new WeaverException(s"Invalid acc() argument: '$invalid'")
      }

      checkType match {
        case Separation =>
          Seq(
            CheckInfo(
              FieldSeparationCheck(field),
              condition.map(ImmediateCondition)
            )
          )
        case Verification =>
          Seq(
            CheckInfo(
              FieldAccessibilityCheck(field),
              condition.map(ImmediateCondition)
            )
          )
      }

    }
    case pred: IR.PredicateInstance => {
      checkType match {
        case Separation =>
          Seq(
            CheckInfo(
              PredicateSeparationCheck(
                pred.predicate.name,
                pred.arguments.map(resolveValue(_, arguments))
              ),
              condition.map(ImmediateCondition)
            )
          )
        case Verification =>
          Seq(
            CheckInfo(
              PredicateAccessibilityCheck(
                pred.predicate.name,
                pred.arguments.map(resolveValue(_, arguments))
              ),
              condition.map(ImmediateCondition)
            )
          )
      }

    }
    case _ => {
      // Otherwise there can be no permission specifiers in this term or its children
      Seq.empty
    }
  }

  def hasImplicitReturn(method: IR.Method): Boolean =
    method.body.lastOption match {
      case None         => true
      case Some(tailOp) => hasImplicitReturn(tailOp)
    }

  // Checks if execution can fall-through a given Op
  def hasImplicitReturn(tailOp: IR.Op): Boolean = tailOp match {
    case r: IR.Return => false
    case _: IR.While  => true
    case iff: IR.If =>
      (iff.ifTrue.lastOption, iff.ifFalse.lastOption) match {
        case (Some(t), Some(f)) => hasImplicitReturn(t) || hasImplicitReturn(f)
        case _                  => true
      }
    case _ => true
  }

  def isImprecise(
      cond: Option[IR.Expression],
      visited: mutable.Set[Predicate] = mutable.Set.empty[Predicate]): Boolean =
    cond match {
      case Some(expr: IR.Expression) =>
        expr match {
          case instance: IR.PredicateInstance =>
            if (visited.contains(instance.predicate)) {
              false
            } else {
              visited += instance.predicate
              isImprecise(Some(instance.predicate.expression), visited)
            }
          case _: IR.Imprecise => true
          case conditional: IR.Conditional =>
            isImprecise(Some(conditional.condition), visited) || isImprecise(
              Some(conditional.ifTrue),
              visited) || isImprecise(Some(conditional.ifFalse), visited)
          case binary: IR.Binary =>
            isImprecise(Some(binary.left), visited) || isImprecise(
              Some(binary.right),
              visited)
          case unary: IR.Unary => isImprecise(Some(unary.operand), visited)
          case _               => false
        }
      case None => false
    }

  def getCallstyle(irMethod: IR.Method) =
    if (irMethod.name == "main")
      MainCallStyle
    else if (isImprecise(irMethod.precondition))
      ImpreciseCallStyle
    else if (isImprecise(irMethod.postcondition))
      PrecisePreCallStyle
    else PreciseCallStyle

  // Changes an expression from an IR expression into a CheckExpression. If an argument lookup
  // mapping is given, it will use this mapping to resolve variables. Otherwise, it will assume
  // any variables are accessible in the current scope.
  def resolveValue(
      input: IR.Expression,
      arguments: Option[Map[IR.Parameter, CheckExpression]] = None
  ): CheckExpression = {
    def resolve(input: IR.Expression) = resolveValue(input, arguments)

    input match {
      // These types can only be used at the "root" of a specification, not in an arbitrary
      // expression
      case _: IR.ArrayMember | _: IR.Imprecise | _: IR.PredicateInstance |
          _: IR.Accessibility =>
        throw new WeaverException("Invalid specification value")

      case n: IR.Var =>
        arguments match {
          case None => CheckExpression.Var(n.name)
          case Some(arguments) =>
            n match {
              case p: IR.Parameter =>
                arguments.getOrElse(
                  p,
                  throw new WeaverException(s"Unknown parameter '${p.name}'")
                )
              case v =>
                throw new WeaverException(s"Unknown variable '${v.name}'")
            }
        }

      case n: IR.FieldMember =>
        CheckExpression.Field(
          resolve(n.root),
          n.field.struct.name,
          n.field.name
        )
      case n: IR.DereferenceMember => CheckExpression.Deref(resolve(n.root))
      case n: IR.Result            => CheckExpression.Result
      case n: IR.IntLit            => CheckExpression.IntLit(n.value)
      case n: IR.CharLit           => CheckExpression.CharLit(n.value)
      case n: IR.BoolLit           => CheckExpression.BoolLit(n.value)
      case n: IR.StringLit         => CheckExpression.StrLit(n.value)
      case n: IR.NullLit           => CheckExpression.NullLit
      case n: IR.Conditional =>
        CheckExpression.Cond(
          resolve(n.condition),
          resolve(n.ifTrue),
          resolve(n.ifFalse)
        )
      case n: IR.Binary => {
        val l = resolve(n.left)
        val r = resolve(n.right)
        n.operator match {
          case IR.BinaryOp.Add      => CheckExpression.Add(l, r)
          case IR.BinaryOp.Subtract => CheckExpression.Sub(l, r)
          case IR.BinaryOp.Divide   => CheckExpression.Div(l, r)
          case IR.BinaryOp.Multiply => CheckExpression.Mul(l, r)
          case IR.BinaryOp.And      => CheckExpression.And(l, r)
          case IR.BinaryOp.Or       => CheckExpression.Or(l, r)
          case IR.BinaryOp.Equal    => CheckExpression.Eq(l, r)
          case IR.BinaryOp.NotEqual =>
            CheckExpression.Not(CheckExpression.Eq(l, r))
          case IR.BinaryOp.Less           => CheckExpression.Lt(l, r)
          case IR.BinaryOp.LessOrEqual    => CheckExpression.LtEq(l, r)
          case IR.BinaryOp.Greater        => CheckExpression.Gt(l, r)
          case IR.BinaryOp.GreaterOrEqual => CheckExpression.GtEq(l, r)
        }
      }
      case n: IR.Unary => {
        val o = resolve(n.operand)
        n.operator match {
          case IR.UnaryOp.Not    => CheckExpression.Not(o)
          case IR.UnaryOp.Negate => CheckExpression.Neg(o)
        }
      }
    }
  }
}
