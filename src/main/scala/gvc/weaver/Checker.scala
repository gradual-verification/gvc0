package gvc.weaver
import gvc.transformer.IRGraph._
import Collector._
import gvc.transformer.{IRGraph, SilverVarId}
import scala.collection.mutable

object Checker {
  type StructIDTracker = Map[scala.Predef.String, StructField]

  class CheckerMethod(
      val method: Method,
      tempVars: Map[SilverVarId, Invoke]
  ) extends CheckMethod {
    val resultVars = mutable.Map[java.lang.String, Var]()

    def resultVar(name: java.lang.String): Var = {
      resultVars.getOrElseUpdate(
        name, {
          val invoke = tempVars.getOrElse(
            SilverVarId(method.name, name),
            throw new WeaverException(s"Missing temporary variable '$name'")
          )

          val retType = invoke.method.returnType.getOrElse(
            throw new WeaverException(
              s"Invalid temporary variable '$name' for void method"
            )
          )
          val tempVar = method.addVar(retType)
          invoke.target = Some(tempVar)

          tempVar
        }
      )
    }
  }

  def insert(program: CollectedProgram): Unit = {
    val runtime = CheckRuntime.addToIR(program.program)

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance
    val structIdFields = program.program.structs
      .map(s => (s.name, s.addField(CheckRuntime.Names.id, IntType)))
      .toMap

    val implementation =
      new CheckImplementation(program.program, runtime, structIdFields)

    program.methods.values.foreach { method =>
      insert(program, method, runtime, implementation)
    }
  }

  private def insert(
      programData: CollectedProgram,
      methodData: CollectedMethod,
      runtime: CheckRuntime,
      implementation: CheckImplementation
  ): Unit = {
    val program = programData.program
    val method = methodData.method
    val checkMethod = new CheckerMethod(method, programData.temporaryVars)

    // `ops` is a function that generates the operations, given the current return value at that
    // position. DO NOT construct the ops before passing them to this method since multiple copies
    // may be required.
    def insertAt(at: Location, ops: Option[Expression] => Seq[Op]): Unit =
      at match {
        case LoopStart(op: While) => ops(None) ++=: op.body
        case LoopEnd(op: While)   => op.body ++= ops(None)
        case Pre(op)              => op.insertBefore(ops(None))
        case Post(op)             => op.insertAfter(ops(None))
        case MethodPre            => ops(None) ++=: method.body
        case MethodPost =>
          methodData.returns.foreach(e => e.insertBefore(ops(e.value)))
          if (methodData.hasImplicitReturn) {
            method.body ++= ops(None)
          }
        case _ => throw new WeaverException(s"Invalid location '$at'")
      }

    // Define condition variables and create a map from term ID to variables
    val trackedConditions = mutable.Map[scala.Int, Var]()
    val sortedConditions = mutable.ListBuffer[(Location, Var, Expression)]()
    def getTrackedCondition(cond: TrackedCondition) = {
      trackedConditions.getOrElseUpdate(cond.id, {
        val flag = method.addVar(BoolType, s"_cond_${cond.id}")
        sortedConditions += ((cond.location, flag, getTrackedConditionValue(cond)))
        flag
      })
    }

    def getConjunction(conj: TrackedConjunction, loc: Location): Option[Expression] =
      conj.values.foldLeft[Option[Expression]](None) {
        case (expr, (cond, flag)) =>
          val flagExpr =
            if (loc == cond.location) {
              getTrackedConditionValue(cond)
            } else {
              getTrackedCondition(cond)
            }

          val value = if (flag) flagExpr else new Unary(UnaryOp.Not, flagExpr)
          expr match {
            case None       => Some(value)
            case Some(expr) => Some(new Binary(BinaryOp.And, expr, value))
          }
      }

    def getDisjunction(disj: TrackedDisjunction, loc: Location): Option[Expression] =
      disj.cases.foldLeft[Option[Expression]](None) {
        case (Some(expr), conj) =>
          getConjunction(conj, loc).map(new Binary(BinaryOp.Or, expr, _))
        case (None, conj) => getConjunction(conj, loc)
      }

    def getTrackedConditionValue(cond: TrackedCondition): Expression =
      cond.when.flatMap(getDisjunction(_, cond.location)) match {
        case None => cond.value.toIR(program, checkMethod, None)
        case Some(when) =>
          new Binary(
            BinaryOp.And,
            when,
            cond.value.toIR(program, checkMethod, None)
          )
      }

    def getCondition(cond: Condition, loc: Location): Option[Expression] = cond match {
      case tracked: TrackedDisjunction => getDisjunction(tracked, loc)
      case cond: ConditionValue =>
        cond.value match {
          case CheckExpression.TrueLit => None
          case value                   => Some(value.toIR(program, checkMethod, None))
        }
    }

    val initializeOps = mutable.ListBuffer[Op]()

    var (primaryOwnedFields, instanceCounter) = methodData.callStyle match {
      case MainCallStyle => {
        val instanceCounter =
          method.addVar(
            new PointerType(IntType),
            CheckRuntime.Names.instanceCounter
          )
        initializeOps += new AllocValue(IntType, instanceCounter)
        (None, instanceCounter)
      }

      case PreciseCallStyle => {
        val instanceCounter =
          method.addParameter(
            new PointerType(IntType),
            CheckRuntime.Names.instanceCounter
          )
        (None, instanceCounter)
      }

      case ImpreciseCallStyle | PrecisePreCallStyle => {
        val ownedFields: Var =
          method.addParameter(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.primaryOwnedFields
          )
        val instanceCounter =
          new FieldMember(ownedFields, runtime.ownedFieldInstanceCounter)
        (Some(ownedFields), instanceCounter)
      }
    }

    def getPrimaryOwnedFields(): Var = primaryOwnedFields.getOrElse {
      val ownedFields = method.addVar(
        runtime.ownedFieldsRef,
        CheckRuntime.Names.primaryOwnedFields
      )
      primaryOwnedFields = Some(ownedFields)

      initializeOps += new Invoke(
        runtime.initOwnedFields,
        List(instanceCounter),
        primaryOwnedFields
      )
      ownedFields
    }

    // Insert the runtime checks
    // Group them by location and condition, so that multiple checks can be contained in a single
    // if block.
    val context = CheckContext(program, checkMethod, implementation, runtime)
    methodData.checks
      .groupBy(c => (c.location, c.when))
      .foreach { case ((loc, when), checks) =>
        val condition = when.flatMap(getCondition(_, loc))
        insertAt(
          loc,
          implementChecks(
            condition,
            checks.map(_.check),
            _,
            getPrimaryOwnedFields,
            instanceCounter,
            context
          )
        )
      }

    val needsToTrackPrecisePerms =
      primaryOwnedFields.isDefined ||
        methodData.calls.exists(c =>
          programData.methods(c.ir.callee.name).callStyle match {
            case ImpreciseCallStyle | PrecisePreCallStyle => true
            case _                                        => false
          }
        )

    // Update the call sites to add any required parameters
    for (call <- methodData.calls) {
      val callee = call.ir.callee match {
        case method: Method => method
        case _: DependencyMethod =>
          throw new WeaverException("Invalid method call")
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
            // Convert precondition into calls to removeAcc
            call.ir.insertBefore(
              callee.precondition.toSeq.flatMap(
                implementation.translate(RemoveMode, _, getPrimaryOwnedFields)
              )
            )

            // Convert postcondition into calls to addAcc
            call.ir.insertAfter(
              callee.postcondition.toSeq.flatMap(
                implementation.translate(AddMode, _, getPrimaryOwnedFields)
              )
            )
          }
        }

        // For precise-pre/imprecise-post, create a temporary set of permissions, add the
        // permissions from the precondition, call the method, and add the temporary set to the
        // primary set
        case PrecisePreCallStyle => {
          val tempSet = method.addVar(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.temporaryOwnedFields
          )

          val createTemp = new Invoke(
            runtime.initOwnedFields,
            List(instanceCounter),
            Some(tempSet)
          )
          val addPermsToTemp = callee.precondition.toSeq
            .flatMap(implementation.translate(AddMode, _, tempSet))
            .toList
          val removePermsFromPrimary = callee.precondition.toSeq
            .flatMap(
              implementation.translate(RemoveMode, _, getPrimaryOwnedFields)
            )
            .toList

          call.ir.insertBefore(
            createTemp :: addPermsToTemp ++ removePermsFromPrimary
          )
          call.ir.arguments :+= tempSet
          call.ir.insertAfter(
            new Invoke(runtime.join, List(getPrimaryOwnedFields, tempSet), None)
          )
        }
      }
    }

    // If a primary owned fields instance is required for this method, add all allocations into it
    addAllocationTracking(
      primaryOwnedFields,
      methodData.allocations,
      implementation,
      runtime
    )

    // Add all conditions that need tracked
    // Group all conditions for a single location and insert in sequence
    // to preserve the correct ordering of conditions.
    sortedConditions
      .groupBy { case (loc, _, _) => loc }
      .foreach {
        case (loc, conds) => insertAt(loc, retVal => {
          conds.map { case (_, flag, value) => new Assign(flag, value) }
        })
    }

    // Finally, add all the initialization ops to the beginning
    initializeOps ++=: method.body
  }

  def addAllocationTracking(
      primaryOwnedFields: Option[Var],
      allocations: List[Op],
      implementation: CheckImplementation,
      runtime: CheckRuntime
  ): Unit = {
    for (ownedFields <- primaryOwnedFields) {
      for (alloc <- allocations) {
        alloc match {
          case alloc: AllocStruct => {
            val structType = alloc.struct
            val idField = new FieldMember(
              alloc.target,
              implementation.structIdField(alloc.struct)
            )
            alloc.insertAfter(
              new Invoke(
                runtime.addStructAcc,
                List(ownedFields, new Int(structType.fields.length - 1)),
                Some(idField)
              )
            )
          }
          case _ =>
            throw new WeaverException(
              "Tracking is only currently supported for struct allocations."
            )
        }
      }
    }
  }

  def implementAccCheck(
      check: FieldPermissionCheck,
      fields: FieldCollection,
      context: CheckContext
  ): Seq[Op] = {
    val field = check.field.toIR(context.program, context.method, None)
    val (mode, perms) = check match {
      case _: FieldSeparationCheck =>
        (SeparationMode, fields.temporaryOwnedFields())
      case _: FieldAccessibilityCheck =>
        (VerifyMode, fields.primaryOwnedFields())
    }
    context.implementation.translateFieldPermission(mode, field, perms)
  }

  def implementPredicateCheck(
      check: PredicatePermissionCheck,
      returnValue: Option[Expression],
      fields: FieldCollection,
      context: CheckContext
  ): Seq[Op] = {
    val instance = new PredicateInstance(
      context.program.predicate(check.predicateName),
      check.arguments.map(_.toIR(context.program, context.method, returnValue))
    )
    val (mode, perms) = check match {
      case _: PredicateSeparationCheck =>
        (SeparationMode, fields.temporaryOwnedFields())
      case _: PredicateAccessibilityCheck =>
        (VerifyMode, fields.primaryOwnedFields())
    }
    context.implementation.translatePredicateInstance(mode, instance, perms)
  }

  case class FieldCollection(
      primaryOwnedFields: () => Var,
      temporaryOwnedFields: () => Var
  )

  case class CheckContext(
      program: Program,
      method: CheckMethod,
      implementation: CheckImplementation,
      runtime: CheckRuntime
  )

  def implementCheck(
      check: Check,
      returnValue: Option[IRGraph.Expression],
      fields: FieldCollection,
      context: CheckContext
  ): Seq[Op] = {
    check match {
      case acc: FieldPermissionCheck =>
        implementAccCheck(
          acc,
          fields,
          context
        )
      case pc: PredicatePermissionCheck =>
        implementPredicateCheck(
          pc,
          returnValue,
          fields,
          context
        )
      case expr: CheckExpression =>
        Seq(
          new Assert(
            expr.toIR(context.program, context.method, returnValue),
            AssertKind.Imperative
          )
        )
    }
  }

  def implementChecks(
      cond: Option[Expression],
      checks: List[Check],
      returnValue: Option[Expression],
      getPrimaryOwnedFields: () => Var,
      instanceCounter: Expression,
      context: CheckContext
  ): Seq[Op] = {
    // Create a temporary owned fields instance when it is required
    var temporaryOwnedFields: Option[Var] = None
    def getTemporaryOwnedFields(): Var = temporaryOwnedFields.getOrElse {
      val tempVar = context.method.method.addVar(
        context.runtime.ownedFieldsRef,
        CheckRuntime.Names.temporaryOwnedFields
      )
      temporaryOwnedFields = Some(tempVar)
      tempVar
    }
    // Collect all the ops for the check
    var ops =
      checks.flatMap(
        implementCheck(
          _,
          returnValue,
          FieldCollection(getPrimaryOwnedFields, getTemporaryOwnedFields),
          context
        )
      )

    // Prepend op to initialize owned fields if it is required
    temporaryOwnedFields.foreach { tempOwned =>
      ops = new Invoke(
        context.runtime.initOwnedFields,
        List(instanceCounter),
        Some(tempOwned)
      ) :: ops
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
}
