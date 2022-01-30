package gvc.weaver
import gvc.transformer.IRGraph._
import Collector._
import gvc.transformer.IRGraph
import scala.collection.mutable

object Checker {
  def insert(program: CollectedProgram): Unit = {
    lazy val runtime = CheckRuntime.addToIR(program.program)

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance
    val structIdFields = program.program.structs
      .map(s => (s.name, s.addField("_id", IntType)))
      .toMap

    program.methods.values.foreach { method => insert(program, method, runtime, structIdFields) }
  }

  private def insert(
      programData: CollectedProgram,
      methodData: CollectedMethod,
      runtime: => CheckRuntime,
      structIdFields: Map[java.lang.String, IRGraph.StructField]
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

    val initializeOps = mutable.ListBuffer[Op]()

    var (primaryOwnedFields, instanceCounter) = methodData.callStyle match {
      case MainCallStyle => {
        val instanceCounter = method.addVar(new PointerType(IntType), "_instanceCounter")
        initializeOps += new AllocValue(IntType, instanceCounter)
        (None, instanceCounter)
      }

      case PreciseCallStyle => {
        val instanceCounter = method.addParameter(new PointerType(IntType), "_instanceCounter")
        (None, instanceCounter)
      }

      case ImpreciseCallStyle | PrecisePreCallStyle => {
        val ownedFields: Var = method.addParameter(runtime.ownedFieldsRef, "_ownedFields")
        val instanceCounter = new FieldMember(ownedFields, runtime.ownedFieldInstanceCounter)
        (Some(ownedFields), instanceCounter)
      }
    }

    def getPrimaryOwnedFields = primaryOwnedFields.getOrElse {
      val ownedFields = method.addVar(runtime.ownedFieldsRef, "_ownedFields")
      // TODO: initOwnedFields could return a newly-allocated struct
      initializeOps += new AllocStruct(runtime.ownedFields, ownedFields)
      initializeOps += new Invoke(runtime.initOwnedFields, List(ownedFields, instanceCounter), None)
      primaryOwnedFields = Some(ownedFields)
      ownedFields
    }

    def implementAccCheck(check: AccessibilityCheck, temporaryOwnedFields: => Expression): Seq[Op] = {
      // Get the `_id` value that identifies the struct instance
      val structId = new FieldMember(
        check.field.root.toIR(program, method, None),
        structIdFields(check.field.structName)
      )

      // Get the number that identifies the struct field
      val fieldToCheck = check.field.getIRField(program)
      val fieldIndex =
        new IRGraph.Int(fieldToCheck.struct.fields.indexOf(fieldToCheck))

      val ops = mutable.ListBuffer[Op]()
      if (check.checkExists) {
        ops += new Invoke(
          runtime.assertAcc,
          List(
            getPrimaryOwnedFields,
            structId,
            fieldIndex
          ),
          None
        )
      }

      if (check.checkSeparate) {
        ops += new Invoke(
          runtime.addDisjointAcc,
          List(
            temporaryOwnedFields,
            structId,
            fieldIndex
          ),
          None
        )
      }

      ops.toList
    }

    def implementCheck(
        check: Check,
        returnValue: Option[IRGraph.Expression],
        temporaryOwnedFields: => Expression
    ): Seq[Op] = {
      check match {
        case acc: AccessibilityCheck => implementAccCheck(acc, temporaryOwnedFields)
        case pc: PredicateCheck =>
          Seq(runtime.callPredicate(pc.predicate, methodData))
        case expr: CheckExpression =>
          Seq(new Assert(
            expr.toIR(program, method, returnValue),
            AssertKind.Imperative
          ))
      }
    }

    def implementChecks(
        cond: Option[Expression],
        checks: List[Check],
        returnValue: Option[Expression]
    ): Seq[Op] = {
      // Create a temporary owned fields instance when it is required
      var temporaryOwnedFields: Option[Var] = None
      def getTemporaryOwnedFields = temporaryOwnedFields.getOrElse {
        val tempVar = method.addVar(runtime.ownedFieldsRef, "_temp_fields")
        temporaryOwnedFields = Some(tempVar)
        tempVar
      }

      // Collect all the ops for the check
      var ops = checks.flatMap(implementCheck(_, returnValue, getTemporaryOwnedFields))

      // Prepend op to initialize owned fields if it is required
      temporaryOwnedFields.foreach { tempOwned =>
        ops = new Invoke(runtime.initOwnedFields, List(instanceCounter), None) :: ops
      }

      // Wrap in an if statement if it is conditional
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
            _
          )
        )
      }

    val needsToTrackPrecisePerms =
      primaryOwnedFields.isDefined ||
      methodData.calls.exists(c => programData.methods(c.ir.callee.name).callStyle match {
        case ImpreciseCallStyle | PrecisePreCallStyle => true
        case _ => false
      })

    // Update the call sites to add any required parameters
    for (call <- methodData.calls) {
      val callee = call.ir.callee match {
        case method: Method => method
        case _: DependencyMethod => throw new WeaverException("Invalid method call")
      }
      val calleeData = programData.methods(callee.name)

      calleeData.callStyle match {
        // No parameters can be added to a main method
        case MainCallStyle => ()

        // Imprecise methods always get the primary owned fields instance directly
        case ImpreciseCallStyle => call.ir.arguments :+= getPrimaryOwnedFields

        case PreciseCallStyle => {
          // Always pass the instance counter
          call.ir.arguments :+= instanceCounter

          // If we need to track precise permisions, add the code at the call site
          if (needsToTrackPrecisePerms) {
            // Convert precondition into calls to addAcc
            call.ir.insertBefore(
              // TODO
              runtime.removePermissionsFromContract(
                callee.precondition,
                getPrimaryOwnedFields,
                structIdFields,
                runtime
              )
            )

            // Convert postcondition into calls to addAcc
            call.ir.insertAfter(
              runtime.addPermissionsFromContract(
                callee.postcondition,
                getPrimaryOwnedFields,
                structIdFields,
                runtime
              )
            )
          }
        }

        // For precise-pre/imprecise-post, create a temporary set of permissions, add the
        // permissions from the precondition, call the method, and add the temporary set to the
        // primary set
        case PrecisePreCallStyle => {
          val tempSet = method.addVar(runtime.ownedFieldsRef, "_temp_fields")
          call.ir.insertBefore(
            new AllocStruct(runtime.ownedFields, tempSet) ::
            new Invoke(runtime.initOwnedFields, List(instanceCounter), None) ::
            runtime.addPermissionsFromContract(callee.precondition, tempSet, structIdFields, runtime).toList
          )

          call.ir.arguments :+= tempSet

          call.ir.insertAfter(new Invoke(runtime.join, List(getPrimaryOwnedFields, tempSet), None))
        }
      }
    }

    // If a primary owned fields instance is required for this method, add all allocations into it
    for (ownedFields <- primaryOwnedFields)
    for (alloc <- methodData.allocations) {
      alloc match {
        case alloc: AllocStruct => {
          val fieldCount = alloc.struct.fields.length - 1
          val id = new FieldMember(alloc.target, structIdFields(alloc.struct.name))
          alloc.insertAfter(new Invoke(runtime.addStructAcc, List(ownedFields, new IRGraph.Int(fieldCount)), Some(id)))
        }
        case _ =>
          throw new WeaverException(
            "Tracking is only currently supported for struct allocations."
          )
      }
    }

    // Finally, add all the initialization ops to the beginning
    initializeOps ++=: method.body
  }
}
