package gvc.weaver
import gvc.transformer.IRGraph._
import Collector._
import gvc.transformer.IRGraph

object Checker {
  def insert(program: CollectedProgram): Unit = {
    program.methods.values.foreach { method => insert(program, method) }
  }

  private def insert(
      programData: CollectedProgram,
      methodData: CollectedMethod
  ): Unit = {
    val program = programData.program
    val method = methodData.method

    // `ops` is a function that generates the operations, given the current return value at that
    // position. DO NOT construct the ops before passing them to this method since multiple copies
    // may be required.
    def insertAt(at: Location, ops: Option[Expression] => Seq[Op]): Unit =
      at match {
        case Invariant(op) => ???
        case Pre(op)       => op.insertBefore(ops(None))
        case Post(op)      => op.insertAfter(ops(None))
        case MethodPre     => ops(None).foreach(_ +=: method.body)
        case MethodPost => {
          methodData.returns.foreach(e => e.insertBefore(ops(e.value)))
          if (methodData.hasImplicitReturn) {
            ops(None).foreach(method.body += _)
          }
        }
      }

    // Define condition variables and create a map from term ID to variables
    val trackedConditions = methodData.conditions
      .map(cond => (cond.id, method.addVar(BoolType, s"_cond_${cond.id}")))
      .toMap

    def getConjunction(conj: TrackedConjunction): Option[Expression] =
      conj.values.foldLeft[Option[Expression]](None) {
        case (expr, (cond, flag)) => {
          val variable = trackedConditions(cond.id)
          val value = if (flag) variable else new Unary(UnaryOp.Not, variable)
          expr match {
            case None       => Some(value)
            case Some(expr) => Some(new Binary(BinaryOp.And, expr, value))
          }
        }
      }

    def getDisjunction(disj: TrackedDisjunction): Option[Expression] =
      disj.cases.foldLeft[Option[Expression]](None) {
        case (Some(expr), conj) =>
          getConjunction(conj).map(new Binary(BinaryOp.Or, expr, _))
        case (None, conj) => getConjunction(conj)
      }

    def getTrackedConditionValue(cond: TrackedCondition): Expression =
      getDisjunction(cond.when) match {
        case None => cond.value.toIR(program, method, None)
        case Some(when) =>
          new Binary(BinaryOp.And, when, cond.value.toIR(program, method, None))
      }

    def getCondition(cond: Condition): Option[Expression] = cond match {
      case tracked: TrackedDisjunction => getDisjunction(tracked)
      case cond: ConditionValue =>
        cond.value match {
          case CheckExpression.TrueLit => None
          case value                   => Some(value.toIR(program, method, None))
        }
    }

    // Insert the required assignments to condition variables
    methodData.conditions.foreach { cond =>
      insertAt(
        cond.location,
        _ =>
          Seq(
            new Assign(
              trackedConditions(cond.id),
              getTrackedConditionValue(cond)
            )
          )
      )
    }

    def implementAccCheck(
        check: AccessibilityCheck,
        runtime: CheckRuntime
    ): Op = {
      val primaryOwnedFields = runtime.resolvePrimaryOwnedFields(methodData)
      val structId = new FieldMember(
        check.field.root.toIR(program, method, None),
        check.field.getIRField(program)
      )
      val fieldToCheck = check.field.getIRField(program)
      val fieldIndex =
        new IRGraph.Int(fieldToCheck.struct.fields.indexOf(fieldToCheck))
      if (check.separating) {
        val temporaryOwnedFields =
          runtime.resolveTemporaryOwnedFields(methodData)
        if (check.unverified) {
          new Invoke(
            runtime.assertDisjointAcc,
            List(
              temporaryOwnedFields,
              primaryOwnedFields,
              structId,
              fieldIndex
            ),
            None
          )
        } else {
          new Invoke(
            runtime.addDisjointAcc,
            List(
              temporaryOwnedFields,
              structId,
              fieldIndex
            ),
            None
          )
        }
      } else {
        new Invoke(
          runtime.assertAcc,
          List(
            primaryOwnedFields,
            structId,
            fieldIndex
          ),
          None
        )
      }
    }
    def implementCheck(
        check: Check,
        runtimeOption: Option[CheckRuntime],
        returnValue: Option[Expression]
    ): Op =
      check match {
        case acc: AccessibilityCheck =>
          runtimeOption match {
            case Some(runtime) => implementAccCheck(acc, runtime)
            case None =>
              throw new WeaverException(
                "Field access tracking is required, but wasn't initialized."
              )
          }
        case expr: CheckExpression =>
          new Assert(
            expr.toIR(program, method, returnValue),
            AssertKind.Imperative
          )
      }
    def implementChecks(
        cond: Option[Expression],
        checks: Seq[Check],
        runtime: Option[CheckRuntime],
        returnValue: Option[Expression]
    ): Seq[Op] = {
      val ops = checks.map(implementCheck(_, runtime, returnValue))
      cond match {
        case None => ops
        case Some(cond) => {
          val iff = new If(cond)
          iff.condition = cond
          ops.foreach(iff.ifTrue += _)
          Seq(iff)
        }
      }
    }

    // Insert the runtime checks
    // Group them by location and condition, so that multiple checks can be contained in a single
    // if block.
    methodData.checks
      .groupBy(c => (c.location, c.when))
      .foreach {
        case ((loc, when), checks) => {
          val condition = getCondition(when)
          insertAt(
            loc,
            implementChecks(
              condition,
              checks.map(_.check),
              programData.runtime,
              _
            )
          )
        }
      }
    programData.runtime match {
      case Some(runtime) => injectSupport(methodData, runtime)
      case None          =>
    }
  }

  private def injectSupport(
      methodData: CollectedMethod,
      runtime: CheckRuntime
  ): Unit = {
    if (methodData.method.name == "main") {
      val instanceCounter = methodData.method.addVar(
        new PointerType(IntType),
        CheckRuntime.Names.instanceCounter
      )
      methodData.method.body.head.insertBefore(
        Seq(
          new AllocValue(new PointerType(IntType), instanceCounter),
          new AssignMember(
            new DereferenceMember(instanceCounter),
            new IRGraph.Int(0)
          )
        )
      )
    }

    if (
      methodData.callStyle == ImpreciseCallStyle || methodData.callStyle == PrecisePreCallStyle
    ) {
      val primaryOwnedFields = runtime.resolvePrimaryOwnedFields(methodData)
      for (alloc <- methodData.allocations) {
        alloc match {
          case str: AllocStruct =>
            runtime.addDynamicStructAccess(str, primaryOwnedFields)
          case _ =>
            throw new WeaverException(
              "Tracking is only currently supported for struct allocations."
            )
        }
      }
    } else {
      if (methodData.method.name != "main")
        methodData.method.addParameter(
          new PointerType(IntType),
          CheckRuntime.Names.instanceCounter
        )
      val instanceCounter =
        methodData.method.getVar(CheckRuntime.Names.instanceCounter).get
      for (alloc <- methodData.allocations) {
        alloc match {
          case str: AllocStruct =>
            runtime.assignIDFromInstanceCounter(str, instanceCounter)
          case _ =>
            throw new WeaverException(
              "Tracking is only currently supported for struct allocations."
            )
        }
      }
    }
    injectCallsiteSupport(
      methodData,
      runtime
    )
  }

  //TODO: To continue implementation, at what point do we need to start tracking permissions in a precise method when
  // we call imprecise methods? Immediately, or right before the first imprecise call?

  private def injectCallsiteSupport(
      methodData: CollectedMethod,
      runtime: CheckRuntime
  ): Unit = {
    val calledImprecise = false
    methodData.calls.foreach(inv => {
      val callStyle = getCallstyle(inv.method)
      callStyle match {
        case Collector.PreciseCallStyle => {
          if (methodData.callStyle != PreciseCallStyle) {
            //convert precondition into calls to addAcc
            //convert postcondition into calls to addAcc
          }
        }
        case Collector.PrecisePreCallStyle => {
          val calledImprecise = true
          val tempOwnedFields = runtime.resolveTemporaryOwnedFields(methodData)
          inv.insertBefore(
            new Invoke(runtime.initOwnedFields, List(tempOwnedFields), None)
          )
          //convert precondition into calls to addAcc

          inv.insertAfter(new Invoke(runtime.join, List(), None))
        }
        case Collector.ImpreciseCallStyle => {
          val calledImprecise = true
          if (methodData.callStyle == PreciseCallStyle) {
            if (
              !methodData.method
                .getVar(CheckRuntime.Names.primaryOwnedFields)
                .isDefined
            ) {
              val primaryOwnedFields = methodData.method.addVar(
                new ReferenceType(runtime.ownedFields),
                CheckRuntime.Names.primaryOwnedFields
              )
              //convert precondition into calls to addAcc

              inv.arguments = inv.arguments ++ List(primaryOwnedFields)
            }
          } else {}

        }
      }
    })
  }
}