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
        case MethodPost =>
          methodData.returns.foreach(e => e.insertBefore(ops(e.value)))
          if (methodData.hasImplicitReturn) {
            ops(None).foreach(method.body += _)
          }
      }

    // Define condition variables and create a map from term ID to variables
    val trackedConditions = methodData.conditions
      .map(cond => (cond.id, method.addVar(BoolType, s"_cond_${cond.id}")))
      .toMap

    def getConjunction(conj: TrackedConjunction): Option[Expression] =
      conj.values.foldLeft[Option[Expression]](None) {
        case (expr, (cond, flag)) =>
          val variable = trackedConditions(cond.id)
          val value = if (flag) variable else new Unary(UnaryOp.Not, variable)
          expr match {
            case None       => Some(value)
            case Some(expr) => Some(new Binary(BinaryOp.And, expr, value))
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
        returnValue: Option[Expression]
    ): Op =
      check match {
        case expr: CheckExpression =>
          new Assert(
            expr.toIR(program, method, returnValue),
            AssertKind.Imperative
          )
        case _ =>
          throw new WeaverException(
            "Unsupported runtime check in the current mode."
          )
      }
    def implementCheckWithTracking(
        check: Check,
        runtime: CheckRuntime,
        returnValue: Option[IRGraph.Expression],
        methodData: CollectedMethod
    ): Op = {
      check match {
        case acc: AccessibilityCheck => implementAccCheck(acc, runtime)
        case pc: PredicateCheck =>
          runtime.callPredicate(pc.predicate, methodData)
        case _ => implementCheck(check, returnValue)
      }
    }
    def implementChecks(
        cond: Option[Expression],
        checks: Seq[Check],
        maybeRuntime: Option[CheckRuntime],
        returnValue: Option[Expression],
        methodData: CollectedMethod
    ): Seq[Op] = {
      val ops = maybeRuntime match {
        case Some(runtime) =>
          checks.map(
            implementCheckWithTracking(_, runtime, returnValue, methodData)
          )
        case None => checks.map(implementCheck(_, returnValue))
      }
      cond match {
        case None => ops
        case Some(cond) =>
          val iff = new If(cond)
          iff.condition = cond
          ops.foreach(iff.ifTrue += _)
          Seq(iff)
      }
    }

    // Insert the runtime checks
    // Group them by location and condition, so that multiple checks can be contained in a single
    // if block.
    methodData.checks
      .groupBy(c => (c.location, c.when))
      .foreach { case ((loc, when), checks) =>
        val condition = getCondition(when)
        insertAt(
          loc,
          implementChecks(
            condition,
            checks.map(_.check),
            programData.runtime,
            _,
            methodData
          )
        )
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
          new AllocValue(IntType, instanceCounter),
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
    methodData.checkedSpecificationLocations.foreach(loc => {
      if (loc.isInstanceOf[AtOp]) {
        loc
          .asInstanceOf[AtOp]
          .op
          .insertAfter(
            new Invoke(
              runtime.initOwnedFields,
              List(
                runtime.resolveTemporaryOwnedFields(methodData)
              ),
              None
            )
          )
      }
    })

    injectCallsiteSupport(
      methodData,
      runtime
    )
  }

  private def injectCallsiteSupport(
      methodData: CollectedMethod,
      runtime: CheckRuntime
  ): Unit = {
    var calledImprecise = false
    methodData.calls.foreach(inv => {
      val callStyle = getCallstyle(inv.ir.method)
      callStyle match {
        case Collector.PreciseCallStyle =>
          if (methodData.callStyle != PreciseCallStyle) {
            //convert precondition into calls to addAcc
            inv.ir.insertBefore(
              runtime.removePermissionsFromContract(
                methodData.method.precondition,
                methodData
              )
            )
            //convert postcondition into calls to addAcc
            inv.ir.insertAfter(
              runtime.addPermissionsFromContract(
                methodData.method.postcondition,
                methodData
              )
            )
          }

        case Collector.PrecisePreCallStyle =>
          if (methodData.callStyle == PreciseCallStyle && !calledImprecise) {
            //initialize primary OwnedFields with the static permissions at the method's callsite
            inv.ir.insertBefore(
              runtime.loadPermissionsBeforeInvocation(inv.vpr, methodData)
            )

            calledImprecise = true
          }
          val tempOwnedFields = runtime.resolveTemporaryOwnedFields(methodData)
          inv.ir.insertBefore(
            new Invoke(runtime.initOwnedFields, List(tempOwnedFields), None)
          )
          //convert precondition into calls to addAcc
          inv.ir.insertAfter(
            new Invoke(
              runtime.join,
              List(
                runtime.resolvePrimaryOwnedFields(methodData),
                tempOwnedFields
              ),
              None
            )
          )

        case Collector.ImpreciseCallStyle =>
          if (methodData.callStyle == PreciseCallStyle) {
            if (!calledImprecise) {
              //initialize primary OwnedFields with the static permissions at the method's callsite
              inv.ir.insertBefore(
                runtime.loadPermissionsBeforeInvocation(inv.vpr, methodData)
              )
              calledImprecise = true
            }
            if (
              methodData.method
                .getVar(CheckRuntime.Names.primaryOwnedFields)
                .isEmpty
            ) {
              val primaryOwnedFields = methodData.method.addVar(
                new ReferenceType(runtime.ownedFields),
                CheckRuntime.Names.primaryOwnedFields
              )
              //convert precondition into calls to addAcc
              inv.ir.insertBefore(
                runtime.removePermissionsFromContract(
                  methodData.method.precondition,
                  methodData
                )
              )

              inv.ir.arguments = inv.ir.arguments ++ List(primaryOwnedFields)
            }
          } else {
            inv.ir.arguments = inv.ir.arguments ++ List(
              runtime.resolvePrimaryOwnedFields(methodData)
            )
          }
      }
    })
  }
}
