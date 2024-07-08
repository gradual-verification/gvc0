package gvc.benchmarking

import scala.collection.mutable
import gvc.transformer.IR
import gvc.weaver._

object BaselineChecker {

  sealed trait CallStyle
  case object PreciseCallStyle extends CallStyle
  case object PrecisePreCallStyle extends CallStyle
  case object ImpreciseCallStyle extends CallStyle
  case object MainCallStyle extends CallStyle

  def check(program: IR.Program, onlyFraming: Boolean = false): Unit = ()

  /*
    val structIds =
      program.structs.map(s => (s.name, s.addField("_id", IR.IntType))).toMap
    val runtime = CheckRuntime.addToIR(program)
    val checks = new CheckImplementation(program, runtime, structIds)
    program.methods.foreach(checkMethod(_, checks, onlyFraming))
  }*/

  def checkFraming(program: IR.Program): Unit =
    check(program, onlyFraming = true)

  private def checkMethod(
      method: IR.Method,
      checks: CheckImplementation,
      onlyFraming: Boolean
  ): Unit = {
    val globalPerms = method.name match {
      case "main" =>
        method.addVar(
          checks.runtime.ownedFieldsRef,
          CheckRuntime.Names.primaryOwnedFields
        )
      case _ =>
        method.addParameter(
          checks.runtime.ownedFieldsRef,
          CheckRuntime.Names.primaryOwnedFields
        )
    }

    val tempPerms = method.addVar(
      checks.runtime.ownedFieldsRef,
      CheckRuntime.Names.temporaryOwnedFields
    )
    val callstyle = getCallstyle(method)

    callstyle match {

      case PreciseCallStyle | PrecisePreCallStyle =>
        val contextPerms = method.addVar(checks.runtime.ownedFieldsRef,
                                         CheckRuntime.Names.contextOwnedFields)

        checkBlock(method.body,
                   checks,
                   contextPerms,
                   tempPerms,
                   globalPerms,
                   onlyFraming)

        // CheckAddRemove mode
        // Check in global perms, add to context perms, remove from global perms.
        val mode = if (onlyFraming) AddRemoveMode else CheckAddRemoveMode
        method.precondition.toSeq
          .flatMap(
            checks
              .translate(mode, _, contextPerms, Some(globalPerms), ValueContext)
          )
          .toList ++=: method.body

        if (hasImplicitReturn(method)) {

          if (callstyle == PrecisePreCallStyle) {
            if (!onlyFraming) {
              method.body ++= method.postcondition.toSeq.flatMap(
                validateSpec(_, contextPerms, tempPerms, checks)
              )
            }
            method.body ++= Seq(
              new IR.Invoke(
                checks.runtime.join,
                List(globalPerms, contextPerms),
                None
              ))

          } else {
            val mode = if (onlyFraming) AddMode else CheckAddMode
            method.body ++= method.postcondition.toSeq
              .flatMap(
                checks.translate(mode,
                                 _,
                                 globalPerms,
                                 Some(contextPerms),
                                 ValueContext)
              )
              .toList
          }
        }
        Seq(
          new IR.Invoke(
            checks.runtime.initOwnedFields,
            List(
              new IR.FieldMember(
                globalPerms,
                ??? // TODO: checks.runtime.ownedFieldInstanceCounter
              )
            ),
            Some(contextPerms)
          )
        ) ++=: method.body
      case ImpreciseCallStyle | MainCallStyle =>
        checkBlock(method.body,
                   checks,
                   globalPerms,
                   tempPerms,
                   globalPerms,
                   onlyFraming)

        if (!onlyFraming) {
          method.precondition.toSeq.flatMap(
            validateSpec(_, globalPerms, tempPerms, checks)
          ) ++=: method.body
        }

        if (!onlyFraming && hasImplicitReturn(method)) {
          method.body ++= method.postcondition.toSeq.flatMap(
            validateSpec(_, globalPerms, tempPerms, checks)
          )
        }

        if (callstyle == MainCallStyle) {
          val instanceCounter = method.addVar(
            new IR.PointerType(IR.IntType),
            CheckRuntime.Names.instanceCounter
          )

          Seq(
            new IR.AllocValue(IR.IntType, instanceCounter),
            new IR.Invoke(
              checks.runtime.initOwnedFields,
              List(instanceCounter),
              Some(globalPerms)
            )
          ) ++=: method.body
        }
    }
  }

  private def equivalentFields(x: IR.Member, y: IR.Member): Boolean = {
    (x, y) match {
      case (xf: IR.FieldMember, yf: IR.FieldMember) =>
        xf.field == yf.field && ((xf.root, yf.root) match {
          case (xr: IR.Var, yr: IR.Var) => xr == yr
          case (xr: IR.FieldMember, yr: IR.FieldMember) =>
            equivalentFields(xr, yr)
          case _ => false
        })
      case _ => false
    }
  }

  private def validateAccess(
      expr: IR.Expression,
      perms: IR.Var,
      checks: CheckImplementation,
      context: SpecificationContext = ValueContext,
      inSpec: Boolean = false,
      fieldAccs: List[IR.Member] = Nil
  ): (Seq[IR.Op], List[IR.Member]) = expr match {
    case acc: IR.Accessibility =>
      // Check framing
      val (ops, fields) = validateAccess(
        acc.member.root,
        perms,
        checks,
        context,
        inSpec,
        fieldAccs
      )
      (ops, acc.member :: fields)

    case cond: IR.Conditional => {
      val (initial, fields) =
        validateAccess(cond.condition, perms, checks, context, false, fieldAccs)
      val (ifTrue, _) =
        validateAccess(cond.ifTrue, perms, checks, context, inSpec, fieldAccs)
      val (ifFalse, _) =
        validateAccess(cond.ifFalse, perms, checks, context, inSpec, fieldAccs)

      if (ifTrue.isEmpty && ifFalse.isEmpty) {
        (initial, fields)
      } else if (ifTrue.isEmpty) {
        val iff = new IR.If(new IR.Unary(IR.UnaryOp.Not, cond.condition))
        iff.ifTrue ++= ifFalse
        (initial :+ iff, fields)
      } else if (ifFalse.isEmpty) {
        val iff = new IR.If(cond.condition)
        iff.ifTrue ++= ifTrue
        (initial :+ iff, fields)
      } else {
        val iff = new IR.If(cond.condition)
        iff.ifTrue ++= ifTrue
        iff.ifFalse ++= ifFalse
        (initial :+ iff, fields)
      }
    }

    case b: IR.Binary => {
      val subSpec = inSpec && b.operator == IR.BinaryOp.And
      val (left, leftFields) =
        validateAccess(b.left, perms, checks, context, subSpec, fieldAccs)
      val (right, rightFields) =
        validateAccess(b.right, perms, checks, context, subSpec, leftFields)

      if (right.isEmpty) {
        (left, leftFields)
      } else {
        b.operator match {
          // If we are in the top-level of a specification, the conditions must all
          // be satisfied anyway, and we cannot switch based on the condition value
          // (e.g. we cannot check if an acc() is true).

          // But, if we are not in a spec, the short-circuiting behavior of AND
          // must be followed
          case IR.BinaryOp.And if !inSpec =>
            val iff = new IR.If(b.left)
            iff.ifTrue ++= right
            (left :+ iff, leftFields)

          case IR.BinaryOp.Or =>
            val iff = new IR.If(new IR.Unary(IR.UnaryOp.Not, b.left))
            iff.ifTrue ++= right
            (left :+ iff, leftFields)

          case _ =>
            (left ++ right, rightFields)
        }
      }
    }

    case u: IR.Unary =>
      validateAccess(u.operand, perms, checks, context, false, fieldAccs)
    case imp: IR.Imprecise =>
      imp.precise match {
        case None => (Seq.empty, fieldAccs)
        case Some(precise) =>
          validateAccess(precise, perms, checks, context, inSpec, fieldAccs)
      }
    case _: IR.Literal | _: IR.Result | _: IR.Var =>
      (Seq.empty, fieldAccs)

    case field: IR.FieldMember =>
      val (rootOps, fields) =
        validateAccess(field.root, perms, checks, context, inSpec, fieldAccs)
      if (fields.exists(equivalentFields(_, field))) {
        (rootOps, fields)
      } else {
        val acc =
          checks.translateFieldPermission(VerifyMode,
                                          field,
                                          perms,
                                          None,
                                          context)
        (rootOps ++ acc, field :: fields)
      }

    case pred: IR.PredicateInstance =>
      var fields = fieldAccs
      val arguments = pred.arguments.flatMap(arg => {
        val (argOps, argFields) =
          validateAccess(arg, perms, checks, context, false, fields)
        fields = argFields
        argOps
      })
      (arguments, fields)

    case _: IR.ArrayMember | _: IR.DereferenceMember =>
      throw new WeaverException("Invalid member")
  }

  private def validateSpec(
      expr: IR.Expression,
      primaryPerms: IR.Var,
      tempPerms: IR.Var,
      checks: CheckImplementation,
      context: SpecificationContext = ValueContext
  ): Seq[IR.Op] = {
    val (access, _) =
      validateAccess(expr, primaryPerms, checks, context, true, Nil)
    val verify = checks.translate(VerifyMode, expr, primaryPerms, None, context)

    if (verify.isEmpty) {
      // If there are no checks in the specification, there will be no separation checks
      access
    } else {
      val separation =
        checks.translate(SeparationMode, expr, tempPerms, None, context)
      if (separation.isEmpty) {
        access ++ verify
      } else {
        Seq.concat(
          access,
          verify,
          Seq(
            new IR.Invoke(
              checks.runtime.initOwnedFields,
              List(
                new IR.FieldMember(
                  primaryPerms,
                  ??? //TODO: checks.runtime.ownedFieldInstanceCounter
                )
              ),
              Some(tempPerms)
            )
          ),
          separation
        )
      }
    }

  }

  private def checkBlock(
      block: IR.Block,
      checks: CheckImplementation,
      perms: IR.Var,
      tempPerms: IR.Var,
      globalPerms: IR.Var,
      onlyFraming: Boolean
  ): Unit = {
    for (op <- block) op match {
      case _: IR.AllocValue | _: IR.AllocArray =>
        throw new WeaverException("Unsupported alloc")

      case alloc: IR.AllocStruct => {
        // TODO: Need to ID allocation
        alloc.insertAfter(checks.trackAllocation(alloc, perms))
      }

      case assert: IR.Assert =>
        assert.kind match {
          case IR.AssertKind.Imperative =>
            val (access, _) = validateAccess(assert.value, perms, checks)
            assert.insertBefore(access)
          case IR.AssertKind.Specification if !onlyFraming =>
            assert.insertAfter(
              validateSpec(assert.value, perms, tempPerms, checks)
            )
          case _ =>
        }

      case assign: IR.Assign => {
        val (access, _) = validateAccess(assign.value, perms, checks)
        assign.insertBefore(access)
      }

      case assign: IR.AssignMember =>
        assign.member match {
          case field: IR.FieldMember =>
            val (valueAccess, valueFields) =
              validateAccess(assign.value, perms, checks)
            val (rootAccess, rootFields) = validateAccess(
              assign.member.root,
              perms,
              checks,
              fieldAccs = valueFields
            )
            assign.insertBefore(
              valueAccess ++
                rootAccess ++
                checks.translateFieldPermission(
                  VerifyMode,
                  field,
                  perms,
                  None,
                  ValueContext
                )
            )
          case _: IR.DereferenceMember | _: IR.ArrayMember =>
            throw new WeaverException("Invalid member")
        }

      case err: IR.Error => {
        val (access, _) = validateAccess(err.value, perms, checks)
        err.insertBefore(access)
      }

      case iff: IR.If =>
        val (condAccess, _) = validateAccess(iff.condition, perms, checks)
        iff.insertBefore(condAccess)

        checkBlock(iff.ifTrue,
                   checks,
                   perms,
                   tempPerms,
                   globalPerms,
                   onlyFraming)

        checkBlock(iff.ifFalse,
                   checks,
                   perms,
                   tempPerms,
                   globalPerms,
                   onlyFraming)

      case ret: IR.Return =>
        val context = ret.value match {
          case None        => ValueContext
          case Some(value) => new ReturnContext(value)
        }

        val valueAccess =
          ret.value.toSeq.flatMap(validateAccess(_, perms, checks) match {
            case (ops, _) => ops
          })

        val validationOps = if (!onlyFraming) {
          valueAccess ++
            block.method.postcondition.toSeq.flatMap(
              validateSpec(
                _,
                perms,
                tempPerms,
                checks,
                context = context
              )
            )
        } else {
          Seq.empty
        }

        ret.insertBefore(validationOps ++ (getCallstyle(block.method) match {
          case PreciseCallStyle =>
            block.method.postcondition.toSeq
              .flatMap(
                checks.translate(AddMode, _, globalPerms, None, context)
              )
              .toList
          case PrecisePreCallStyle =>
            Seq(
              new IR.Invoke(
                checks.runtime.join,
                List(globalPerms, perms),
                None
              ))
          case _ => Seq.empty
        }))
      case loop: IR.While =>
        val preAccessibility = validateAccess(
          loop.condition,
          perms,
          checks
        )._1 ++ (if (!onlyFraming)
                   validateSpec(loop.invariant, perms, tempPerms, checks)
                 else Seq.empty)
        loop.insertBefore(
          preAccessibility
        )

        checkBlock(loop.body,
                   checks,
                   perms,
                   tempPerms,
                   globalPerms,
                   onlyFraming)

        val postAccessibility = validateAccess(
          loop.condition,
          perms,
          checks
        )._1 ++ (if (!onlyFraming)
                   validateSpec(loop.invariant, perms, tempPerms, checks)
                 else Seq.empty)
        loop.body ++= postAccessibility

      case invoke: IR.Invoke =>
        // Pre-conditions are handled inside callee
        var fields: List[IR.Member] = Nil
        val argAccess = invoke.arguments.flatMap(arg => {
          val (argOps, argFields) =
            validateAccess(arg, perms, checks, fieldAccs = fields)
          fields = argFields
          argOps
        })
        val targetAccess = invoke.target.toSeq.flatMap(t =>
          validateAccess(t, perms, checks, fieldAccs = fields)._1)
        invoke.insertBefore(argAccess ++ targetAccess)
        invoke.callee match {
          case method: IR.Method =>
            invoke.arguments = invoke.arguments :+ perms
          case method: IR.DependencyMethod =>
        }
      case fold: IR.Fold     =>
      case unfold: IR.Unfold =>
      case _                 =>
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
      visited: mutable.Set[IR.Predicate] = mutable.Set.empty[IR.Predicate]): Boolean =
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

}
