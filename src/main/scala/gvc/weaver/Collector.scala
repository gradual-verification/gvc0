package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IRGraph._
import viper.silver.ast.MethodCall
import viper.silver.{ast => vpr}
import viper.silicon.state.CheckPosition
import viper.silicon.state.LoopPosition

object Collector {
  sealed trait Location
  sealed trait AtOp extends Location { val op: Op }
  case class Pre(override val op: Op) extends AtOp
  case class Post(override val op: Op) extends AtOp
  case class LoopStart(override val op: Op) extends AtOp
  case class LoopEnd(override val op: Op) extends AtOp
  case object MethodPre extends Location
  case object MethodPost extends Location

  sealed trait Condition
  case class ConditionValue(value: CheckExpression) extends Condition
  case class TrackedCondition(
      id: scala.Int,
      location: Location,
      value: CheckExpression,
      when: TrackedDisjunction
  )
  case class TrackedConjunction(values: List[(TrackedCondition, Boolean)])
  case class TrackedDisjunction(cases: List[TrackedConjunction])
      extends Condition

  case class RuntimeCheck(location: Location, check: Check, when: Condition)

  sealed trait CallStyle
  case object PreciseCallStyle extends CallStyle
  case object PrecisePreCallStyle extends CallStyle
  case object ImpreciseCallStyle extends CallStyle
  case object MainCallStyle extends CallStyle

  class CollectedMethod(
      val method: Method,
      val conditions: List[TrackedCondition],
      val checks: List[RuntimeCheck],
      val returns: List[Return],
      val hasImplicitReturn: Boolean,
      val calls: List[CollectedInvocation],
      val allocations: List[Op],
      val callStyle: CallStyle,
      val checkedSpecificationLocations: Set[Location]
  )

  class CollectedProgram(
      val program: Program,
      val methods: Map[scala.Predef.String, CollectedMethod]
  )

  case class CollectedInvocation(ir: Invoke, vpr: MethodCall)

  def collect(irProgram: Program, vprProgram: vpr.Program): CollectedProgram = {
    val checks = collectChecks(vprProgram)

    val methods = irProgram.methods
      .map(m => 
        (m.name, collect(
          irProgram,
          vprProgram,
          m,
          vprProgram.findMethod(m.name),
          checks
        )))
      .toMap

    new CollectedProgram(
      program = irProgram,
      methods = methods
    )
  }

  private class ConditionTerm(val id: scala.Int) {
    val conditions = mutable.Set[Logic.Conjunction]()
  }

  private sealed trait ViperLocation
  private object ViperLocation {
    case object Value extends ViperLocation
    case object PreInvoke extends ViperLocation
    case object PostInvoke extends ViperLocation
    case object PreLoop extends ViperLocation
    case object PostLoop extends ViperLocation
    case object InvariantLoopStart extends ViperLocation
    case object InvariantLoopEnd extends ViperLocation
    
    def loop(loopPosition: LoopPosition): ViperLocation = loopPosition match {
      case LoopPosition.After => ViperLocation.PreLoop
      case LoopPosition.Before => ViperLocation.PostLoop
      case LoopPosition.Beginning => ViperLocation.InvariantLoopStart
      case LoopPosition.End => ViperLocation.InvariantLoopEnd
    }

    def forIR(irLocation: Location, vprLocation: ViperLocation): Location = irLocation match {
      case at: AtOp => vprLocation match {
        case ViperLocation.PreInvoke |
          ViperLocation.PreLoop |
          ViperLocation.Value => Pre(at.op)
        case ViperLocation.PostInvoke |
          ViperLocation.PostLoop => Post(at.op)
        case ViperLocation.InvariantLoopStart => LoopStart(at.op)
        case ViperLocation.InvariantLoopEnd => LoopEnd(at.op)
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
    condition: vpr.Exp,
  )

  private object ViperBranch {
    def apply(branch: (vpr.Exp, vpr.Node, Option[CheckPosition]), program: vpr.Program) = branch match {
      case (condition, source, Some(CheckPosition.GenericNode(invoke: vpr.MethodCall))) => {
        // This must be a method pre-condition or post-condition
        val callee = program.findMethod(invoke.methodName)
        val location: ViperLocation =
          if (isContained(source, callee.posts)) ViperLocation.PostInvoke
          else ViperLocation.PreInvoke
        new ViperBranch(invoke, location, condition)
      }

      case (condition, source, Some(CheckPosition.Loop(inv, position))) => {
        // This must be an invariant
        if (inv.tail.nonEmpty) throw new WeaverException("Invalid loop invariant")
        new ViperBranch(inv.head, ViperLocation.loop(position), condition)
      }

      case (condition, source, None) => {
        new ViperBranch(source, ViperLocation.Value, condition)
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

  private type ViperCheckMap = mutable.HashMap[scala.Int, mutable.ListBuffer[ViperCheck]]

  // Convert the verifier's check map into a ViperCheckMap
  private def collectChecks(vprProgram: vpr.Program): ViperCheckMap = {
    val vprChecks = viper.silicon.state.runtimeChecks.getChecks
    val collected = new ViperCheckMap()

    for ((pos, checks) <- vprChecks) {
      val (node, location) = pos match {
        case CheckPosition.GenericNode(node) => (node, ViperLocation.Value)
        case CheckPosition.Loop(invariants, position) => {
          if (invariants.tail.nonEmpty) throw new WeaverException("Invalid loop invariant")
          (invariants.head, ViperLocation.loop(position))
        }
      }

      val list = collected.getOrElseUpdate(node.uniqueIdentifier, mutable.ListBuffer())
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

  private def collect(
      irProgram: Program,
      vprProgram: vpr.Program,
      irMethod: Method,
      vprMethod: vpr.Method,
      vprChecks: ViperCheckMap
  ): CollectedMethod = {
    // A mapping of Viper node IDs to the corresponding IR op.
    // This is used for locating the correct insertion of conditionals.
    val locations = mutable.Map[scala.Int, Location]()

    // A list of `return` statements in the IR method, used for inserting any runtime checks that
    // the postcondition may require.
    val exits = mutable.ListBuffer[Return]()
    // A list of invocations and allocations, used for inserting permission tracking
    val invokes = mutable.ListBuffer[CollectedInvocation]()
    val allocations = mutable.ListBuffer[Op]()

    // The collection of conditions that are used in runtime checks. Not all conditions may be
    // necessary after simplification.
    val conditions = mutable.Map[(Location, CheckExpression), ConditionTerm]()

    // The collection of runtime checks that are required, mapping a runtime check to the list of
    // conjuncts where one conjunct must be true in order for the runtime check to occur.
    // Note: Uses a List as a Map so that the order is preserved in the way that the verifier
    // determines (this is important for acc checks of a nested field, for example).
    val checks =
      mutable.Map[Location, mutable.ListBuffer[(Check, mutable.Set[Logic.Conjunction])]]()

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

    // Collects all permissions in the given specification, and adds checks for them at the given
    // location.
    // TODO: Factor this out
    def traversePermissions(
        location: Location,
        spec: Expression,
        arguments: Option[Map[Parameter, CheckExpression]],
        condition: Option[CheckExpression]
    ): Seq[RuntimeCheck] = spec match {
      // Imprecise expressions just needs the precise part checked.
      // TODO: This should also enable framing checks.
      case imp: Imprecise => {
        imp.precise.toSeq.flatMap(
          traversePermissions(location, _, arguments, condition)
        )
      }

      // And expressions just traverses both parts
      case and: Binary if and.operator == BinaryOp.And => {
        val left = traversePermissions(location, and.left, arguments, condition)
        val right =
          traversePermissions(location, and.right, arguments, condition)
        left ++ right
      }

      // A condition expression traverses each side with its respective condition, joined with the
      // existing condition if provided to support nested conditionals.
      case cond: Conditional => {
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
          traversePermissions(location, cond.ifTrue, arguments, Some(trueCond))
        val falsePerms = traversePermissions(
          location,
          cond.ifFalse,
          arguments,
          Some(falseCond)
        )
        truePerms ++ falsePerms
      }

      // A single accessibility check
      case acc: Accessibility => {
        val field = resolveValue(acc.member, arguments) match {
          case f: CheckExpression.Field => f
          case invalid =>
            throw new WeaverException(s"Invalid acc() argument: '$invalid'")
        }

        Seq(
          RuntimeCheck(
            location,
            AccessibilityCheck(field, true, true),
            ConditionValue(condition.getOrElse(CheckExpression.TrueLit))
          )
        )
      }

      case pred: PredicateInstance => {
        Seq(
          RuntimeCheck(
            location,
            PredicateCheck(pred.predicate, pred.arguments),
            ConditionValue(condition.getOrElse(CheckExpression.TrueLit))
          )
        )
      }

      case _ => {
        // Otherwise there can be no permission specifiers in this term or its children
        Seq.empty
      }
    }

    // Finds all the runtime checks required by the given Viper node, and adds them at the given
    // IR location.
    // `loopInvs` is the list of the invariants from all the loops that contain this position.
    def check(node: vpr.Node, loc: Location, methodCall: Option[vpr.Method], loopInvs: List[vpr.Exp]): Unit = {
      for (vprCheck <- vprChecks.get(node.uniqueIdentifier).toSeq.flatten) {
        val condition = branchCondition(vprCheck.conditions, loopInvs)

        val checkLocation = loc match {
          case at: AtOp => vprCheck.location match {
            case ViperLocation.Value => methodCall match {
              case Some(method) if isContained(vprCheck.context, method.posts) =>
                Post(at.op)
              case _ => Pre(at.op)
            }
            case ViperLocation.PreLoop | ViperLocation.PreInvoke => Pre(at.op)
            case ViperLocation.PostLoop | ViperLocation.PostInvoke => Post(at.op)
            case ViperLocation.InvariantLoopStart => LoopStart(at.op)
            case ViperLocation.InvariantLoopEnd => LoopEnd(at.op)
          }
          case _ => {
            if (vprCheck.location != ViperLocation.Value)
              throw new WeaverException("Invalid check location")
            loc
          }
        }

        // TODO: Split apart ANDed checks?
        val check = Check.fromViper(vprCheck.check, irProgram, irMethod)

        val locationChecks = checks.getOrElseUpdate(checkLocation, mutable.ListBuffer())
        val conditions = locationChecks.find { case (c, _) => c == check } match {
          case Some((_, conditions)) => conditions
          case None =>
            val conditions = mutable.Set[Logic.Conjunction]()
            locationChecks += (check -> conditions)
            conditions
        }

        conditions += condition

        if (check.isInstanceOf[AccessibilityCheck] && (loc == MethodPre || loc == MethodPost || vprCheck.location != ViperLocation.Value)) {
          needsFullPermissionChecking += checkLocation
        }
      }
    }

    // Recursively collects all runtime checks
    def checkAll(node: vpr.Node, loc: Location, methodCall: Option[vpr.Method], loopInvs: List[vpr.Exp]): Unit =
      node.visit { case n => check(n, loc, methodCall, loopInvs) }

    // Combines indexing and runtime check collection for a given Viper node. Indexing must be
    // completed first, since the conditions on a runtime check may be at locations contained in
    // the same node.
    def visit(op: Op, node: vpr.Node, loopInvs: List[vpr.Exp]): Unit = {
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
          loop.invs.foreach { i => checkAll(i, loc, None, loopInvs) }
        }

        case n => {
          indexAll(n, loc)
          checkAll(n, loc, None, loopInvs)
        }
      }
    }

    def visitBlock(irBlock: Block, vprBlock: vpr.Seqn, loopInvs: List[vpr.Exp]): Unit = {
      var vprOps = vprBlock.ss.toList
      for (irOp <- irBlock) {
        vprOps = (irOp, vprOps) match {
          case (irIf: If, (vprIf: vpr.If) :: vprRest) => {
            visit(irIf, vprIf, loopInvs)
            visitBlock(irIf.ifTrue, vprIf.thn, loopInvs)
            visitBlock(irIf.ifFalse, vprIf.els, loopInvs)
            vprRest
          }
          case (irWhile: While, (vprWhile: vpr.While) :: vprRest) => {
            visit(irWhile, vprWhile, loopInvs)
            // Supports only a single invariant
            val newInvs = vprWhile.invs.headOption.map(_ :: loopInvs).getOrElse(loopInvs)
            visitBlock(irWhile.body, vprWhile.body, newInvs)
            vprRest
          }
          case (irInvoke: Invoke, (vprInvoke: vpr.MethodCall) :: vprRest) => {
            invokes += CollectedInvocation(irInvoke, vprInvoke)
            visit(irInvoke, vprInvoke, loopInvs)
            vprRest
          }
          case (irAlloc: AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
            visit(irAlloc, vprAlloc, loopInvs)
            vprRest
          }
          case (irAlloc: AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
            visit(irAlloc, vprAlloc, loopInvs)
            vprRest
          }
          case (
                irAssign: Assign,
                (vprAssign: vpr.LocalVarAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign, loopInvs)
            vprRest
          }
          case (
                irAssign: AssignMember,
                (vprAssign: vpr.FieldAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign, loopInvs)
            vprRest
          }
          case (irAssert: Assert, vprRest)
              if irAssert.kind == AssertKind.Imperative =>
            vprRest
          case (irAssert: Assert, (vprAssert: vpr.Assert) :: vprRest)
              if irAssert.kind == AssertKind.Specification => {
            visit(irAssert, vprAssert, loopInvs)
            vprRest
          }
          case (irFold: Fold, (vprFold: vpr.Fold) :: vprRest) => {
            visit(irFold, vprFold, loopInvs)
            vprRest
          }
          case (irUnfold: Unfold, (vprUnfold: vpr.Unfold) :: vprRest) => {
            visit(irUnfold, vprUnfold, loopInvs)
            vprRest
          }
          case (irError: Error, (vprError: vpr.Assert) :: vprRest) => {
            visit(irError, vprError, loopInvs)
            vprRest
          }
          case (irReturn: Return, vprRest) if irReturn.value.isEmpty => {
            exits += irReturn
            vprRest
          }
          case (irReturn: Return, (vprReturn: vpr.LocalVarAssign) :: vprRest)
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
    }

    // Converts the stack of branch conditions from the verifier to a logical conjunction
    def branchCondition(branches: List[ViperBranch], loopInvs: List[vpr.Exp]): Logic.Conjunction = {

      branches.foldRight[Logic.Conjunction](Logic.Conjunction())((b, conj) => {
        val irLoc = locations.getOrElse(
          b.at.uniqueIdentifier,
          throw new WeaverException(
            s"Could not find location for ${b.at}"
          )
        )

        val position = b.location match {
          // Special case for when the verifier uses positions tagged as the beginning of the loop
          // outside of the loop body. In this case, just use the after loop position.
          case ViperLocation.InvariantLoopStart if !isContained(b.at, loopInvs) =>
            ViperLocation.PostLoop
          case p => p
        }

        val loc = ViperLocation.forIR(irLoc, position)
        val value = CheckExpression.fromViper(b.condition, irMethod)
        val (unwrapped, flag) = value match {
          case CheckExpression.Not(negated) => (negated, false)
          case other                        => (other, true)
        }
        val nextId = conditions.size
        val cond = conditions.getOrElseUpdate((loc, unwrapped), new ConditionTerm(nextId))
        cond.conditions += conj

        conj & Logic.Term(cond.id, flag)
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

    // Check if execution can fall-through to the end of the method
    // It is valid to only check the last operation since we don't allow early returns
    val implicitReturn: Boolean = irMethod.body.lastOption match {
      case None         => true
      case Some(tailOp) => hasImplicitReturn(tailOp)
    }

    // Collect and simplify all the conditions
    val usedConditions = mutable.Map[scala.Int, TrackedCondition]()
    val conditionIndex = conditions.map { case ((loc, value), cond) =>
      (cond.id, (loc, value, Logic.Disjunction(cond.conditions.toSet)))
    }

    // Converts a logical conjunction to the actual expression that it represents
    def convertConjunction(conjunction: Logic.Conjunction): TrackedConjunction =
      TrackedConjunction(
        conjunction.terms.toSeq.sorted
          .map(t => (getCondition(t.id), t.value))
          .toList
      )

    // Converts a logical disjunction to the actual expression that it represents
    // TODO: pull out common factors?
    def convertDisjunction(disjunction: Logic.Disjunction): TrackedDisjunction =
      TrackedDisjunction(
        disjunction.conjuncts.toSeq.sorted
          .map(convertConjunction(_))
          .toList
      )

    // Maps the logical ID to the actual condition that it represents.
    // Creates the actual condition if it does not exist.
    def getCondition(id: scala.Int): TrackedCondition = {
      usedConditions.getOrElseUpdate(
        id, {
          val (loc, value, when) = conditionIndex(id)
          val simplified = Logic.simplify(when)
          val condition = convertDisjunction(simplified)
          TrackedCondition(id, loc, value, condition)
        }
      )
    }

    // Get all checks (grouped by their location) and simplify their conditions
    val collectedChecks = mutable.ListBuffer[RuntimeCheck]()
    for ((loc, locChecks) <- checks)
    for ((check, conditions) <- locChecks) {
      val simplified = Logic.simplify(Logic.Disjunction(conditions.toSet))
      val condition = convertDisjunction(simplified)
      collectedChecks += RuntimeCheck(loc, check, condition)
    }

    // Traverse the specifications for statements that require full permission checks
    for (location <- needsFullPermissionChecking) {
      val (spec, arguments) = location match {
        case at: AtOp => at.op match {
          case op: Invoke if op.method.precondition.isDefined =>
            (
              op.method.precondition.get,
              Some(
                op.method.parameters.zip(op.arguments.map(resolveValue(_))).toMap
              )
            )
          case op: While if op.invariant.isDefined => (op.invariant.get, None)
          case op: Assert => (op.value, None)
          case _ => throw new WeaverException(
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

      // TODO: These checks are only for separation, not existence
      collectedChecks ++= traversePermissions(
        location,
        spec,
        arguments,
        None
      )
    }

    // Wrap up all the results
    new CollectedMethod(
      method = irMethod,
      conditions = usedConditions.values.toSeq.sortBy(_.id).toList,
      checks = collectedChecks.toList,
      returns = exits.toList,
      hasImplicitReturn = implicitReturn,
      calls = invokes.toList,
      allocations = allocations.toList,
      callStyle = getCallstyle(irMethod),
      checkedSpecificationLocations = needsFullPermissionChecking.toSet
    )
  }

  // Checks if execution can fall-through a given Op
  private def hasImplicitReturn(tailOp: Op): Boolean = tailOp match {
    case r: Return => false
    case _: While  => true
    case iff: If =>
      (iff.ifTrue.lastOption, iff.ifFalse.lastOption) match {
        case (Some(t), Some(f)) => hasImplicitReturn(t) || hasImplicitReturn(f)
        case _                  => true
      }
    case _ => true
  }

  def isImprecise(cond: Option[Expression]) = cond match {
    case Some(_: Imprecise) => true
    case _                  => false
  }

  def getCallstyle(irMethod: Method) =
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
  private def resolveValue(
      input: Expression,
      arguments: Option[Map[Parameter, CheckExpression]] = None
  ): CheckExpression = {
    def resolve(input: Expression) = resolveValue(input, arguments)

    input match {
      // These types can only be used at the "root" of a specification, not in an arbitrary
      // expression
      case _: ArrayMember | _: Imprecise | _: PredicateInstance |
          _: Accessibility =>
        throw new WeaverException("Invalid specification value")

      case n: Var =>
        arguments match {
          case None => CheckExpression.Var(n.name)
          case Some(arguments) =>
            n match {
              case p: Parameter =>
                arguments.getOrElse(
                  p,
                  throw new WeaverException(s"Unknown parameter '${p.name}'")
                )
              case v =>
                throw new WeaverException(s"Unknown variable '${v.name}'")
            }
        }

      case n: FieldMember =>
        CheckExpression.Field(
          resolve(n.root),
          n.field.struct.name,
          n.field.name
        )
      case n: DereferenceMember => CheckExpression.Deref(resolve(n.root))
      case n: Result            => CheckExpression.Result
      case n: Int               => CheckExpression.IntLit(n.value)
      case n: Char              => CheckExpression.CharLit(n.value)
      case n: Bool              => CheckExpression.BoolLit(n.value)
      case n: String            => CheckExpression.StrLit(n.value)
      case n: Null              => CheckExpression.NullLit
      case n: Conditional =>
        CheckExpression.Cond(
          resolve(n.condition),
          resolve(n.ifTrue),
          resolve(n.ifFalse)
        )
      case n: Binary => {
        val l = resolve(n.left)
        val r = resolve(n.right)
        n.operator match {
          case BinaryOp.Add      => CheckExpression.Add(l, r)
          case BinaryOp.Subtract => CheckExpression.Sub(l, r)
          case BinaryOp.Divide   => CheckExpression.Div(l, r)
          case BinaryOp.Multiply => CheckExpression.Mul(l, r)
          case BinaryOp.And      => CheckExpression.And(l, r)
          case BinaryOp.Or       => CheckExpression.Or(l, r)
          case BinaryOp.Equal    => CheckExpression.Eq(l, r)
          case BinaryOp.NotEqual =>
            CheckExpression.Not(CheckExpression.Eq(l, r))
          case BinaryOp.Less           => CheckExpression.Lt(l, r)
          case BinaryOp.LessOrEqual    => CheckExpression.LtEq(l, r)
          case BinaryOp.Greater        => CheckExpression.Gt(l, r)
          case BinaryOp.GreaterOrEqual => CheckExpression.GtEq(l, r)
        }
      }
      case n: Unary => {
        val o = resolve(n.operand)
        n.operator match {
          case UnaryOp.Not    => CheckExpression.Not(o)
          case UnaryOp.Negate => CheckExpression.Neg(o)
        }
      }
    }
  }
}
