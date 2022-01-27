package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IRGraph._
import viper.silver.ast.MethodCall
import viper.silver.{ast => vpr}

object Collector {
  sealed trait Location
  case class Pre(val op: Op) extends Location
  case class Post(val op: Op) extends Location
  case class Invariant(val op: Op) extends Location
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

  class CollectedMethod(
      val method: Method,
      val conditions: List[TrackedCondition],
      val checks: List[RuntimeCheck],
      val returns: List[Return],
      val hasImplicitReturn: Boolean,
      val calls: List[CollectedInvocation],
      val allocations: List[Op],
      val callStyle: CallStyle,
      val requiresFieldAccessTracking: Boolean
  )

  class CollectedProgram(
      val program: Program,
      val methods: Map[java.lang.String, CollectedMethod],
      val runtime: Option[CheckRuntime]
  )

  case class CollectedInvocation(ir: Invoke, vpr: MethodCall)

  def collect(irProgram: Program, vprProgram: vpr.Program): CollectedProgram = {
    var runtime: Option[CheckRuntime] = None
    val methods = irProgram.methods
      .map(m => {
        val collected = collect(
          irProgram,
          vprProgram,
          m,
          vprProgram.findMethod(m.name)
        )
        if (collected.requiresFieldAccessTracking) {
          runtime = Some(CheckRuntime.addToIR(irProgram))
        }
        (m.name, collected)
      })
      .toMap
    new CollectedProgram(
      program = irProgram,
      methods = methods,
      runtime = runtime
    )
  }

  private class ConditionTerm(val id: scala.Int) {
    val conditions = mutable.Set[Logic.Conjunction]()
  }

  private case class ViperLocation(node: Integer, child: Option[Integer])
  private object ViperLocation {
    def apply(node: vpr.Node, child: vpr.Node) =
      new ViperLocation(node.uniqueIdentifier, Some(child.uniqueIdentifier))
    def apply(node: vpr.Node) =
      new ViperLocation(node.uniqueIdentifier, None)
  }

  private def collect(
      irProgram: Program,
      vprProgram: vpr.Program,
      irMethod: Method,
      vprMethod: vpr.Method
  ): CollectedMethod = {
    // Get all checks from the verifier
    val vprChecks = viper.silicon.state.runtimeChecks.getChecks

    // A mapping of Viper nodes to the corresponding location in the IR.
    // This is used for locating the correct insertion of conditionals.
    val locations = mutable.Map[ViperLocation, Location]()

    // A list of `return` statements in the IR method, used for inserting any runtime checks that
    // the postcondition may require.
    val exits = mutable.ListBuffer[Return]()
    val invokes = mutable.ListBuffer[CollectedInvocation]()
    val allocations = mutable.ListBuffer[Op]()

    // The collection of conditions that are used in runtime checks. Not all conditions may be
    // necessary after simplification.
    val conditions = mutable.Map[(Location, CheckExpression), ConditionTerm]()

    // The collection of runtime checks that are required, mapping a runtime check to the list of
    // conjuncts where one conjunct must be true in order for the runtime check to occur.
    val checks =
      mutable.Map[(Location, Check), mutable.Set[Logic.Conjunction]]()

    // A set of all locations that need the full specification walked to find all conditions. Used
    // to implement the semantics of the separating conjunction. Pre-calculates a set so that the
    // same location is not checked twice.
    val needsFullPermissionChecking = mutable.Set[Location]()

    // Indexing adds the node to the mapping of Viper locations to IR locations
    def index(node: vpr.Node, loc: Location): Unit =
      locations += ViperLocation(node) -> loc

    // Indexes the given node and all of its child nodes
    def indexAll(node: vpr.Node, loc: Location): Unit =
      node.visit { case n => locations += ViperLocation(n) -> loc }

    // Collects all permissions in the given specification, and adds checks for them at the given
    // location.
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

        // TODO: Add checks for framing (these can overlap)

        Seq(
          RuntimeCheck(
            location,
            AccessibilityCheck(field, true, false),
            ConditionValue(condition.getOrElse(CheckExpression.TrueLit))
          )
        )
      }

      case pred: PredicateInstance => {
        Seq(
          RuntimeCheck(
            location,
            PredicateCheck(pred),
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
    // IR location

    var requiresFieldAccessTracking = false
    def check(node: vpr.Node, loc: Location): Unit = {
      for (check <- vprChecks.get(node).toSeq.flatten) {
        val condition = branchCondition(check.branchInfo)

        // TODO: Split apart ANDed checks?
        Check.fromViper(check, irMethod) match {
          case acc: AccessibilityCheck =>
            requiresFieldAccessTracking = true
            if (!node.contains(check.context)) {
              // If the context is outside of the current node, it must have been generated by a
              // specification. In this case, we need to walk the entire specification and disregard
              // what the verifier thinks can be skipped, in order to satisfy the properties of the
              // separating conjunction.

              needsFullPermissionChecking += loc
              // TODO: Remove debugging
              println(s"METHOD: ${irMethod.name}")
              println(s"AT: $node")
              println(s"CHECK: $check")
              println(s"LOCATION: $loc")
              println(s"CONTEXT: ${check.context}")
            }
            checks.getOrElseUpdate((loc, acc), mutable.Set()) += condition
          case check => {
            checks.getOrElseUpdate((loc, check), mutable.Set()) += condition
          }
        }
      }
    }

    // Recursively collects all runtime checks
    def checkAll(node: vpr.Node, loc: Location): Unit =
      node.visit { case n => check(n, loc) }

    // Combines indexing and runtime check collection for a given Viper node. Indexing must be
    // completed first, since the conditions on a runtime check may be at locations contained in
    // the same node.
    def visit(op: Op, node: vpr.Node): Unit = {
      val loc = Pre(op)
      node match {
        case iff: vpr.If => {
          index(iff, loc)
          indexAll(iff.cond, loc)

          check(iff, loc)
          checkAll(iff.cond, loc)
        }

        case call: vpr.MethodCall => {
          val method = vprProgram.findMethod(call.methodName)
          indexAll(call, loc)
          method.pres.foreach { p =>
            p.visit { case pre =>
              locations += ViperLocation(node, pre) -> Pre(op)
            }
          }
          method.posts.foreach { p =>
            p.visit { case post =>
              locations += ViperLocation(node, post) -> Post(op)
            }
          }

          checkAll(call, loc)
        }

        case loop: vpr.While => {
          index(loop, loc)
          indexAll(loop.cond, loc)
          loop.invs.foreach(indexAll(_, Invariant(op)))

          check(loop, loc)
          checkAll(loop.cond, loc)
          loop.invs.foreach { i => checkAll(i, Invariant(op)) }
        }

        case n => {
          indexAll(n, loc)
          checkAll(n, loc)
        }
      }
    }

    def visitBlock(irBlock: Block, vprBlock: vpr.Seqn): Unit = {
      var vprOps = vprBlock.ss.toList
      for (irOp <- irBlock) {
        vprOps = (irOp, vprOps) match {
          case (irIf: If, (vprIf: vpr.If) :: vprRest) => {
            visit(irIf, vprIf)
            visitBlock(irIf.ifTrue, vprIf.thn)
            visitBlock(irIf.ifFalse, vprIf.els)
            vprRest
          }
          case (irWhile: While, (vprWhile: vpr.While) :: vprRest) => {
            visit(irWhile, vprWhile)
            visitBlock(irWhile.body, vprWhile.body)
            vprRest
          }
          case (irInvoke: Invoke, (vprInvoke: vpr.MethodCall) :: vprRest) => {
            invokes += CollectedInvocation(irInvoke, vprInvoke)
            visit(irInvoke, vprInvoke)
            vprRest
          }
          case (irAlloc: AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
            visit(irAlloc, vprAlloc)
            vprRest
          }
          case (irAlloc: AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            allocations += irAlloc
            visit(irAlloc, vprAlloc)
            vprRest
          }
          case (
                irAssign: Assign,
                (vprAssign: vpr.LocalVarAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign)
            vprRest
          }
          case (
                irAssign: AssignMember,
                (vprAssign: vpr.FieldAssign) :: vprRest
              ) => {
            visit(irAssign, vprAssign)
            vprRest
          }
          case (irAssert: Assert, vprRest)
              if irAssert.kind == AssertKind.Imperative =>
            vprRest
          case (irAssert: Assert, (vprAssert: vpr.Assert) :: vprRest)
              if irAssert.kind == AssertKind.Specification => {
            visit(irAssert, vprAssert)
            vprRest
          }
          case (irFold: Fold, (vprFold: vpr.Fold) :: vprRest) => {
            visit(irFold, vprFold)
            vprRest
          }
          case (irUnfold: Unfold, (vprUnfold: vpr.Unfold) :: vprRest) => {
            visit(irUnfold, vprUnfold)
            vprRest
          }
          case (irError: Error, (vprError: vpr.Assert) :: vprRest) => {
            visit(irError, vprError)
            vprRest
          }
          case (irReturn: Return, vprRest) if irReturn.value.isEmpty => {
            exits += irReturn
            vprRest
          }
          case (irReturn: Return, (vprReturn: vpr.LocalVarAssign) :: vprRest)
              if irReturn.value.isDefined => {
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
    def branchCondition(
        branches: Seq[(vpr.Exp, vpr.Node, Option[vpr.Node])]
    ): Logic.Conjunction = {
      branches.foldRight(Logic.Conjunction())((b, conj) =>
        b match {
          case (branch, position, origin) => {
            val vprLoc = origin match {
              case None         => ViperLocation(position)
              case Some(origin) => ViperLocation(origin, position)
            }

            val loc = locations.getOrElse(
              vprLoc,
              throw new WeaverException(
                s"Could not find location for $origin, $position"
              )
            )
            val value = CheckExpression.fromViper(branch, irMethod)
            val (unwrapped, flag) = value match {
              case CheckExpression.Not(negated) => (negated, false)
              case other                        => (other, true)
            }

            val nextId = conditions.size
            val cond = conditions.getOrElseUpdate(
              (loc, unwrapped),
              new ConditionTerm(nextId)
            )
            cond.conditions += conj

            conj & Logic.Term(cond.id, flag)
          }
        }
      )
    }

    // Index pre-conditions and add required runtime checks
    vprMethod.pres.foreach(indexAll(_, MethodPre))
    vprMethod.pres.foreach(checkAll(_, MethodPre))

    // Loop through each operation and collect checks
    visitBlock(irMethod.body, vprMethod.body.get)

    // Index post-conditions and add required runtime checks
    vprMethod.posts.foreach(indexAll(_, MethodPost))
    vprMethod.posts.foreach(checkAll(_, MethodPost))

    // Check if execution can fall-through to the end of the method
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
    for (((loc, check), conditions) <- checks) {
      val simplified = Logic.simplify(Logic.Disjunction(conditions.toSet))
      val condition = convertDisjunction(simplified)
      collectedChecks += RuntimeCheck(loc, check, condition)
    }

    // Traverse the specifications for statements that require full permission checks
    for (location <- needsFullPermissionChecking) {
      val (spec, arguments) = location match {
        case Pre(op: Invoke) if op.method.precondition.isDefined =>
          (
            op.method.precondition.get,
            Some(
              op.method.parameters.zip(op.arguments.map(resolveValue(_))).toMap
            )
          )
        case Invariant(op: While) if op.invariant.isDefined =>
          (op.invariant.get, None)
        case MethodPost if irMethod.postcondition.isDefined =>
          (irMethod.postcondition.get, None)
        case Pre(op: Assert) =>
          (op.value, None)
        case _ =>
          throw new WeaverException(
            "Could not locate specification for permission checking: " + location
              .toString()
          )
      }

      // TODO: If only a single separated permission is collected, make it non-separating since it
      // will never overlap

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
      requiresFieldAccessTracking = requiresFieldAccessTracking
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

  def getCallstyle(irMethod: Method) = if (isImprecise(irMethod.precondition))
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
