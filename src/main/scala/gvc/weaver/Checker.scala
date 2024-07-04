package gvc.weaver

import gvc.transformer.IR
import scala.collection.mutable
import scala.annotation.tailrec
import CheckRuntime.Names

object Checker {
  sealed trait CallStyle
  case object PermissionsOptional extends CallStyle
  case object PermissionsRequired extends CallStyle
  case object PermissionsElided extends CallStyle

  type StructIDTracker = Map[String, IR.StructField]

  def insert(program: ProgramDependencies): Unit = {
    val runtime = CheckRuntime.addToIR(program.program)

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance
    val structIdFields = program.program.structs
      .map(s => (s.name, s.addField(CheckRuntime.Names.id, IR.IntType)))
      .toMap

    val implementation =
      new CheckImplementation(program.program, runtime, structIdFields)

    program.methods.values.foreach { method =>
      insert(program, method, runtime, implementation)
    }

    InstanceCounter.inject(program.program, structIdFields)
  }

  // Assumes that there is a single return statement at the end of the method.
  // This assumption is guaranteed during transformation by the
  // ReturnSimplification pass.
  private def insertBeforeReturn(
    block: IR.Block,
    ops: Option[IR.Expression] => Seq[IR.Op]
  ) : Unit = block.lastOption match {
    case Some(ret: IR.Return) => ret.insertBefore(ops(ret.value))
    case _ => block ++= ops(None)
  }

  private def insertAt(
    at: Location,
    method: IR.Method,
    ops: Option[IR.Expression] => Seq[IR.Op]
  ): Unit = at match {
    case LoopStart(op: IR.While) => ops(None) ++=: op.body
    case LoopEnd(op: IR.While)   => op.body ++= ops(None)
    case Pre(op)                 => op.insertBefore(ops(None))
    case Post(op)                => op.insertAfter(ops(None))
    case MethodPre               => ops(None) ++=: method.body
    case MethodPost              => insertBeforeReturn(method.body, ops)
    case _ => throw new WeaverException(s"Invalid location '$at'")
  }

  trait PermissionScope {
    def requirePermissions: IR.Expression
    def optionalPermissions(generate: IR.Expression => Seq[IR.Op]): Seq[IR.Op]
    def optionalPermissions: IR.Expression
    def trackingPermissions: Boolean
  }

  class RequiredPermissions(permissions: IR.Expression) extends PermissionScope {
    def requirePermissions = permissions
    def optionalPermissions(generate: IR.Expression => Seq[IR.Op]): Seq[IR.Op] =
      generate(permissions)
    def optionalPermissions: IR.Expression = permissions
    def trackingPermissions = true
  }

  class OptionalPermissions(permissions: IR.Expression) extends PermissionScope {
    def requirePermissions: IR.Expression =
      throw new WeaverException("Required permissions inside optional permission scope")
    def optionalPermissions(generate: IR.Expression => Seq[IR.Op]): Seq[IR.Op] = {
      val cond = new IR.If(
        new IR.Binary(IR.BinaryOp.NotEqual, permissions, new IR.NullLit()))
      cond.ifTrue ++= generate(permissions)
      List(cond)
    }
    def optionalPermissions: IR.Expression = permissions
    def trackingPermissions: Boolean = false
  }

  object NoPermissions extends PermissionScope {
    def requirePermissions: IR.Expression =
      throw new WeaverException("No permission object available")
    def optionalPermissions(generate: IR.Expression => Seq[IR.Op]): Seq[IR.Op] =
      Seq.empty
    def optionalPermissions: IR.Expression = new IR.NullLit()
    def trackingPermissions: Boolean = false
  }

  private def addPermissionsVar(method: IR.Method, impl: CheckImplementation): IR.Var = {
    method.addVar(impl.runtime.ownedFieldsRef, Names.primaryOwnedFields)
  }
  
  private def addPermissionsParam(method: IR.Method, impl: CheckImplementation): IR.Var =
    method.addParameter(impl.runtime.ownedFieldsRef, Names.primaryOwnedFields)

  private def initPermissions(perms: IR.Var, impl: CheckImplementation): IR.Op = {
    new IR.Invoke(impl.runtime.initOwnedFields, Nil, Some(perms))
  }

  private def addMethodPerms(method: IR.Method, impl: CheckImplementation): IR.Var =
    method.name match {
      case "main" => {
        val perms = addPermissionsVar(method, impl)
        initPermissions(perms, impl) +=: method.body
        perms
      }

      case _ => addPermissionsParam(method, impl)
    }
    
  private def getCallStyle(dep: MethodDependencies): CallStyle = {
    if (dep.returnsPerms) {
      if (dep.requiresPerms) PermissionsRequired
      else if (dep.modifiesPerms && dep.method.name != "main") PermissionsOptional
      else PermissionsElided
    } else {
      PermissionsElided
    }
  }

  private def getPermissions(
    dep: ScopeDependencies,
    impl: CheckImplementation,
    parent: Option[PermissionScope] = None
  ): PermissionScope = {
    dep match {
      case m: MethodDependencies if (m.returnsPerms && m.requiresPerms) =>
        new RequiredPermissions(addMethodPerms(m.method, impl))
      case m: MethodDependencies if (m.returnsPerms && m.modifiesPerms) =>
        new OptionalPermissions(addMethodPerms(m.method, impl))
      case w: WhileDependencies if w.returnsPerms =>
        parent.getOrElse(throw new WeaverException("Parent permissions required"))
      case dep if dep.requiresPerms => {
        // Requires perms but does not return (or inherit) them
        // Need to reconstruct from the spec
        val variable = addPermissionsVar(dep.block.method, impl)
        val spec = dep match {
          case m: MethodDependencies => m.method.precondition
          case w: WhileDependencies => Some(w.op.invariant)
        }
        spec.foreach(p =>
          impl.translate(AddMode, p, variable, None, ValueContext) ++=: dep.block)
        new IR.Invoke(impl.runtime.initOwnedFields, Nil, Some(variable)) +=: dep.block
        new RequiredPermissions(variable)
      }
      case _ => NoPermissions
    }
  }

  private def insert(
    programData: ProgramDependencies,
    methodData: MethodDependencies,
    runtime: CheckRuntime,
    impl: CheckImplementation
  ): Unit = {
    val method = methodData.method

    // Create the permissions scope
    // Adds a parameter to receive OwnedFields, if necessary
    val permissions = getPermissions(methodData, impl, None)

    val conditions = methodData.conditions.map(c =>
      c -> method.addVar(IR.BoolType, "_cond")).toMap

    val context = CheckContext(
      program = programData.program,
      method = method,
      conditions = conditions,
      permissions = permissions,
      implementation = impl,
      runtime = runtime)

    insert(programData, methodData, context)

    // Add all conditions that need tracked
    // Group all conditions for a single location and insert in sequence
    // to preserve the correct ordering of conditions.
    methodData.conditions
      .groupBy(_.location)
      .foreach {
        case (loc, conds) =>
          insertAt(loc, method, retVal => {
            val instrs = mutable.ListBuffer[IR.Op]()
            conds.foreach(
              c =>
                instrs += new IR.Assign(conditions(c),
                                        c.value.toIR(programData.program, method, retVal)))
            instrs
          })
      }
  }

  // Creates a temporary set of permissions, 
  private def useTempPermissions(call: IR.Invoke, perms: IR.Expression, context: CheckContext) = {
    // Need to create temporary set and merge after
    val impl = context.implementation
    val runtime = context.runtime
    val tempPerms = context.method.addVar(
      runtime.ownedFieldsRef, Names.temporaryOwnedFields)

    call.insertBefore(
      new IR.Invoke(runtime.initOwnedFields, Nil, Some(tempPerms)))

    val pre = call.callee match {
      case m: IR.Method => m.precondition
      case _: IR.DependencyMethod =>
        throw new WeaverException("Attempting to add permissions to library method")
    }

    pre.foreach(pre =>
      call.insertBefore(impl.translate(
        AddRemoveMode, pre, tempPerms, Some(perms), new CallSiteContext(call))))

    call.arguments :+= tempPerms

    call.insertAfter(new IR.Invoke(runtime.join, List(perms, tempPerms), None))
  }

  // Adds permissions to a method
  private def addPermissions(call: IR.Invoke, context: CheckContext, program: ProgramDependencies) = {
    val dep = program.methods(call.callee.name)
    getCallStyle(dep) match {
      case PermissionsRequired if dep.inheritsPerms =>
        call.arguments :+= context.permissions.requirePermissions
      case PermissionsRequired =>
        // Permissions are returned, but not inherited (i.e., precise pre,
        // imprecise post)
        useTempPermissions(call, context.permissions.requirePermissions, context)
      case PermissionsOptional =>
        // Since permissions are optional, the presence of permissions is never
        // checked, so it doesn't matter that we send more permissions than are
        // required. (Thus we don't need to special-case precise pre, imprecise
        // post.)
        call.arguments :+= context.permissions.optionalPermissions
      case PermissionsElided if dep.returnsPerms =>
        // Returns permissions dynamically, but they are elided since it does
        // not modify (or check) permissions
        ()
      case PermissionsElided => {
        // Elided because the method is static

        // Remove permissions in the pre-condition before calling
        dep.method.precondition.foreach(pre => {
          call.insertBefore(context.permissions.optionalPermissions(perms =>
            context.implementation.translate(RemoveMode, pre, perms, None, new CallSiteContext(call))))
        })

        // Add permissions in the post-condition after the call
        dep.method.postcondition.foreach(post => {
          call.insertAfter(context.permissions.optionalPermissions(perms =>
            context.implementation.translate(AddMode, post, perms, None, new CallSiteContext(call))))
        })
      }
    }
  }

  private def insert(
      programData: ProgramDependencies,
      scope: ScopeDependencies,
      context: CheckContext
  ): Unit = {
    val program = programData.program

    // Insert the runtime checks
    // Group them by location and condition, so that multiple checks can be contained in a single
    // if block.
    for ((loc, checkData) <- groupChecks(scope.checks)) {
      insertAt(loc, context.method, retVal => {
        val ops = mutable.ListBuffer[IR.Op]()

        // Create a temporary owned fields instance when it is required
        var temporaryOwnedFields: Option[IR.Var] = None

        def getTemporaryOwnedFields(): IR.Var =
          temporaryOwnedFields.getOrElse {
            val tempVar = context.method.addVar(
              context.runtime.ownedFieldsRef,
              CheckRuntime.Names.temporaryOwnedFields
            )
            temporaryOwnedFields = Some(tempVar)
            tempVar
          }

        for ((cond, checks) <- checkData) {
          val condition = cond.map(context.getCondition(_))
          ops ++= implementChecks(
            condition,
            checks.map(_.check),
            retVal,
            getTemporaryOwnedFields,
            context
          )
        }

        // Prepend op to initialize owned fields if it is required
        temporaryOwnedFields.foreach { tempOwned =>
          new IR.Invoke(
            context.runtime.initOwnedFields,
            Nil,
            Some(tempOwned)
          ) +=: ops
        }

        ops
      })
    }

    // Update the call sites to add permission tracking/passing.
    // It is important that this gets done after checks are inserted so that
    // the permission handling code binds closer to the call sites than checks.
    // For example, checks required for a callee's pre-condition must be done
    // before the permissions in the callee's pre-condition are removed.
    for (call <- scope.calls) {
      call.callee match {
        // No parameters can be added to a main method or library methods
        case _: IR.DependencyMethod => ()
        case m if m.name == "main" => ()
        case _: IR.Method => addPermissions(call, context, programData)
      }
    }

    // If a primary owned fields instance is required for this method, add all allocations into it
    for (alloc <- scope.allocations) {
      addAllocationTracking(alloc, context)
    }

    for (child <- scope.children) {
      val perms = getPermissions(
        child,
        context.implementation,
        Some(context.permissions))
      insert(programData, child, context.copy(permissions = perms))
    }
  }

  def addAllocationTracking(
    alloc: IR.AllocStruct,
    context: CheckContext
  ): Unit = {
    context.permissions match {
      case NoPermissions => ()
      case _ => {
        alloc.insertAfter(context.implementation.trackAllocation(alloc, context.permissions.optionalPermissions))
      }
    }
  }

  def implementAccCheck(
      check: FieldPermissionCheck,
      returnValue: Option[IR.Expression],
      fields: FieldCollection,
      context: CheckContext
  ): Seq[IR.Op] = {
    val field = check.field.toIR(context.program, context.method, returnValue)
    val (mode, perms) = check match {
      case _: FieldSeparationCheck =>
        (SeparationMode, fields.temporaryOwnedFields())
      case _: FieldAccessibilityCheck =>
        (VerifyMode, fields.primaryOwnedFields())
    }
    context.implementation.translateFieldPermission(mode,
                                                    field,
                                                    perms,
                                                    None,
                                                    ValueContext)
  }

  def implementPredicateCheck(
      check: PredicatePermissionCheck,
      returnValue: Option[IR.Expression],
      fields: FieldCollection,
      context: CheckContext
  ): Seq[IR.Op] = {
    val instance = new IR.PredicateInstance(
      context.program.predicate(check.predicateName),
      check.arguments.map(_.toIR(context.program, context.method, returnValue))
    )
    val (mode, perms) = check match {
      case _: PredicateSeparationCheck =>
        (SeparationMode, fields.temporaryOwnedFields())
      case _: PredicateAccessibilityCheck =>
        (VerifyMode, fields.primaryOwnedFields())
    }
    context.implementation.translatePredicateInstance(mode,
                                                      instance,
                                                      perms,
                                                      None,
                                                      ValueContext)
  }

  case class FieldCollection(
      primaryOwnedFields: () => IR.Expression,
      temporaryOwnedFields: () => IR.Expression
  )

  case class CheckContext(
      program: IR.Program,
      method: IR.Method,
      conditions: Map[TrackedCondition, IR.Var],
      permissions: PermissionScope,
      implementation: CheckImplementation,
      runtime: CheckRuntime
  ) {
    private def foldConditionList(conds: List[Condition],
                          op: IR.BinaryOp): IR.Expression = {
      conds
        .foldLeft[Option[IR.Expression]](None) {
          case (Some(expr), cond) =>
            Some(new IR.Binary(op, expr, getCondition(cond)))
          case (None, cond) => Some(getCondition(cond))
        }
        .getOrElse(throw new WeaverException("Invalid empty condition list"))
    }

    def getCondition(cond: Condition): IR.Expression = cond match {
      case ImmediateCondition(expr) => expr.toIR(program, method, None)
      case cond: TrackedCondition   => conditions(cond)
      case NotCondition(value) =>
        new IR.Unary(IR.UnaryOp.Not, getCondition(value))
      case AndCondition(values) => foldConditionList(values, IR.BinaryOp.And)
      case OrCondition(values)  => foldConditionList(values, IR.BinaryOp.Or)
    }
  }

  def implementCheck(
      check: Check,
      returnValue: Option[IR.Expression],
      getTemporaryOwnedFields: () => IR.Expression,
      context: CheckContext
  ): Seq[IR.Op] = {
    check match {
      case acc: FieldPermissionCheck =>
        implementAccCheck(
          acc,
          returnValue,
          FieldCollection(
            () => context.permissions.requirePermissions,
            getTemporaryOwnedFields),
          context
        )
      case pc: PredicatePermissionCheck =>
        implementPredicateCheck(
          pc,
          returnValue,
          FieldCollection(
            () => context.permissions.requirePermissions,
            getTemporaryOwnedFields),
          context
        )
      case expr: CheckExpression =>
        Seq(
          new IR.Assert(
            expr.toIR(context.program, context.method, returnValue),
            IR.AssertKind.Imperative
          )
        )
    }
  }

  def implementChecks(
      cond: Option[IR.Expression],
      checks: List[Check],
      returnValue: Option[IR.Expression],
      getTemporaryOwnedFields: () => IR.Var,
      context: CheckContext
  ): Seq[IR.Op] = {
    // Collect all the ops for the check
    var ops =
      checks.flatMap(
        implementCheck(
          _,
          returnValue,
          getTemporaryOwnedFields,
          context
        )
      )

    // Wrap in an if statement if it is conditional
    cond match {
      case None => ops
      case Some(cond) =>
        val iff = new IR.If(cond)
        iff.condition = cond
        ops.foreach(iff.ifTrue += _)
        Seq(iff)
    }
  }

  def groupChecks(items: Seq[RuntimeCheck])
    : List[(Location, List[(Option[Condition], List[RuntimeCheck])])] = {
    items
      .toList
      .groupBy(_.location)
      .toList
      .map {
        case (loc, checks) =>
          val groups = groupConditions(checks)
          val sorted = orderChecks(groups)
          (loc, groupAdjacentConditions(sorted).map {
            case (cond, checks) => (cond, checks)
          })
      }
  }

  // Groups conditions but does not change order
  @tailrec
  def groupAdjacentConditions(
      items: List[RuntimeCheck],
      acc: List[(Option[Condition], List[RuntimeCheck])] = Nil
  ): List[(Option[Condition], List[RuntimeCheck])] = {
    items match {
      case Nil => acc
      case head :: rest => {
        val (same, remaining) = rest.span(_.when == head.when)
        groupAdjacentConditions(remaining, acc :+ (head.when, head :: same))
      }
    }
  }

  // Groups conditions in a stable-sort manner (the first items in each group are in order, etc.),
  // but allows ordering changes
  def groupConditions(items: List[RuntimeCheck]): List[RuntimeCheck] = {
    val map = mutable
      .LinkedHashMap[Option[Condition], mutable.ListBuffer[RuntimeCheck]]()
    for (check <- items) {
      val list = map.getOrElseUpdate(check.when, mutable.ListBuffer())
      list += check
    }

    map.flatMap { case (_, checks) => checks }.toList
  }

  def orderChecks(checks: List[RuntimeCheck]) =
    checks.sortBy(c =>
      c.check match {
        case acc: FieldAccessibilityCheck => nesting(acc.field)
        case _                            => Int.MaxValue
    })(Ordering.Int)

  def nesting(expr: CheckExpression): Int = expr match {
    case b: CheckExpression.Binary =>
      Math.max(nesting(b.left), nesting(b.right)) + 1
    case c: CheckExpression.Cond =>
      Math
        .max(nesting(c.cond), Math.max(nesting(c.ifTrue), nesting(c.ifFalse))) + 1
    case d: CheckExpression.Deref =>
      nesting(d.operand) + 1
    case f: CheckExpression.Field =>
      nesting(f.root) + 1
    case u: CheckExpression.Unary =>
      nesting(u.operand) + 1
    case _: CheckExpression.Literal | _: CheckExpression.Var |
        CheckExpression.Result =>
      1
  }
}
