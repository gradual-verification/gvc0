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

    def implementCheck(check: Check, returnValue: Option[Expression]): Op =
      check match {
        case AccessibilityCheck(field, separating) => ???
        case expr: CheckExpression =>
          new Assert(
            expr.toIR(program, method, returnValue),
            AssertKind.Imperative
          )
      }

    def implementChecks(
        cond: Option[Expression],
        checks: Seq[Check],
        returnValue: Option[Expression]
    ): Seq[Op] = {
      val ops = checks.map(implementCheck(_, returnValue))
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
          insertAt(loc, implementChecks(condition, checks.map(_.check), _))
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
    val sourceOfInstanceCounter: Var =
      if (
        methodData.callStyle == ImprecisePostCallStyle || methodData.callStyle == ImprecisePreCallStyle
      )
        methodData.method.addParameter(
          new ReferenceType(runtime.ownedFields),
          CheckRuntime.Names.ownedFieldsPrimary
        )
      else if (
        methodData.calls.exists(call =>
          isImprecise(call.method.precondition) || isImprecise(
            call.method.postcondition
          )
        )
      )
        methodData.method.addVar(
          new ReferenceType(runtime.ownedFields),
          CheckRuntime.Names.ownedFieldsPrimary
        )
      else if (methodData.method.name == "main") {
        methodData.method.addVar(
          new PointerType(IntType),
          CheckRuntime.Names.instanceCounter
        )
      } else {
        methodData.method.addParameter(
          new PointerType(IntType),
          CheckRuntime.Names.instanceCounter
        )
      }
    injectAllocationSupport(
      sourceOfInstanceCounter,
      runtime,
      methodData.allocations
    )

  }

  private def injectAllocationSupport(
      sourceOfInstanceCounter: Var,
      runtime: CheckRuntime,
      allocations: List[IRGraph.Op]
  ): Unit = {
    if (sourceOfInstanceCounter.name == CheckRuntime.Names.instanceCounter)
      for (alloc <- allocations) {
        alloc match {
          case str: AllocStruct =>
            runtime.addDynamicStructAccess(str, sourceOfInstanceCounter)
          case _ =>
            throw new WeaverException(
              "Tracking is only currently supported for struct allocations."
            )
        }
      }
    else {
      for (alloc <- allocations) {
        alloc match {
          case str: AllocStruct =>
            runtime.assignIDFromInstanceCounter(str, sourceOfInstanceCounter)
          case _ =>
            throw new WeaverException(
              "Tracking is only currently supported for struct allocations."
            )
        }
      }
    }
  }
}
