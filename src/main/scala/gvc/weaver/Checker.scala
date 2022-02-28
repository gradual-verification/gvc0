package gvc.weaver
import gvc.transformer.IRGraph._
import Collector._
import gvc.transformer.IRGraph
import scala.collection.mutable

object Checker {

  class PredicateImplementation {
    val addition: mutable.Map[Predicate, MethodDefinition] =
      mutable.Map[Predicate, MethodDefinition]()
    val removal: mutable.Map[Predicate, MethodDefinition] =
      mutable.Map[Predicate, MethodDefinition]()
    val check: mutable.Map[Predicate, MethodDefinition] =
      mutable.Map[Predicate, MethodDefinition]()
  }

  case class OwnedFieldsSet(
      primary: Expression,
      temporary: Expression
  )
  type StructIDTracker = Map[scala.Predef.String, StructField]
  type PermissionHandler = (
      FieldMember,
      OwnedFieldsSet,
      StructIDTracker
  ) => Invoke
  type PredicateHandler = (
      Predicate,
      List[Expression],
      OwnedFieldsSet,
      StructIDTracker
  ) => Invoke

  def insert(program: CollectedProgram): Unit = {
    lazy val runtime = CheckRuntime.addToIR(program.program)

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance
    val structIdFields = program.program.structs
      .map(s => (s.name, s.addField(CheckRuntime.Names.id, IntType)))
      .toMap

    val predicateImplementations = new PredicateImplementation()

    program.methods.values.foreach { method =>
      insert(program, method, runtime, structIdFields, predicateImplementations)
    }
  }

  private def insert(
      programData: CollectedProgram,
      methodData: CollectedMethod,
      runtime: => CheckRuntime,
      structIdFields: Map[scala.Predef.String, StructField],
      predicates: PredicateImplementation
  ): Unit = {
    val program = programData.program
    val method = methodData.method

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
    def getPrimaryOwnedFields = primaryOwnedFields.getOrElse {
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

    def implementAccCheck(
        check: AccessibilityCheck,
        temporaryOwnedFields: => Expression,
        primaryOwnedFields: => Expression
    ): Seq[Op] = {
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
            temporaryOwnedFields,
            primaryOwnedFields,
            structId,
            fieldIndex,
            new String(
              "Field access runtime check failed for struct " + fieldToCheck.struct.name + "." + fieldToCheck.name
            )
          ),
          None
        )
      }

      if (check.checkSeparate) {
        ops += new Invoke(
          runtime.addAcc,
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
        temporaryOwnedFields: => Expression,
        primaryOwnedFields: => Expression
    ): Seq[Op] = {
      check match {
        case acc: AccessibilityCheck =>
          implementAccCheck(acc, temporaryOwnedFields, primaryOwnedFields)
        case pc: PredicateCheck =>
          Seq(
            resolveCheckPredicate(
              pc.predicate,
              pc.args,
              OwnedFieldsSet(
                primaryOwnedFields,
                temporaryOwnedFields
              ),
              structIdFields
            )
          )
        case expr: CheckExpression =>
          Seq(
            new Assert(
              expr.toIR(program, method, returnValue),
              AssertKind.Imperative
            )
          )
      }
    }

    def resolvePredicateDefinition(
        pred: Predicate,
        predMap: mutable.Map[Predicate, MethodDefinition],
        prefix: scala.Predef.String,
        fieldAccessMutator: PermissionHandler,
        structFields: StructIDTracker,
        predicateHandler: PredicateHandler
    ): MethodDefinition = {
      if (predMap.contains(pred)) {
        predMap(pred)
      } else {
        val predicateMethod =
          program.addMethod(prefix + pred.name, None)
        pred.parameters.foreach(param => {
          predicateMethod.addParameter(param.valueType.get, param.name)
        })

        val temporary = predicateMethod.addParameter(
          new ReferenceType(runtime.ownedFields),
          CheckRuntime.Names.temporaryOwnedFields
        )
        val primary = predicateMethod.addParameter(
          new ReferenceType(runtime.ownedFields),
          CheckRuntime.Names.primaryOwnedFields
        )
        translateSpec(
          pred.expression,
          fieldAccessMutator,
          OwnedFieldsSet(primary, temporary),
          structFields,
          predicateHandler
        ).foreach(op => predicateMethod.body += op)
        predMap += (pred -> predicateMethod)
        predicateMethod
      }
    }

    def implementChecks(
        cond: Option[Expression],
        checks: List[Check],
        returnValue: Option[Expression]
    ): Seq[Op] = {
      // Create a temporary owned fields instance when it is required
      var temporaryOwnedFields: Option[Var] = None
      def getTemporaryOwnedFields: Var = temporaryOwnedFields.getOrElse {
        val tempVar = method.addVar(
          runtime.ownedFieldsRef,
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
            getTemporaryOwnedFields,
            getPrimaryOwnedFields
          )
        )

      // Prepend op to initialize owned fields if it is required
      temporaryOwnedFields.foreach { tempOwned =>
        ops = new Invoke(
          runtime.initOwnedFields,
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

    def resolveCheckPredicate(
        pred: Predicate,
        args: List[Expression],
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val defn = resolvePredicateDefinition(
        pred,
        predicates.check,
        CheckRuntime.Names.checkPrefix,
        assertFieldAccess,
        structIdFields,
        resolveCheckPredicate
      )
      new Invoke(
        defn,
        args ++ List(
          ownedFieldsSet.temporary,
          ownedFieldsSet.primary
        ),
        None
      )
    }

    def resolveAdditionPredicate(
        pred: Predicate,
        args: List[Expression],
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val defn = resolvePredicateDefinition(
        pred,
        predicates.addition,
        CheckRuntime.Names.addPrefix,
        addFieldAccess,
        structIdFields,
        resolveAdditionPredicate
      )
      new Invoke(
        defn,
        args ++ List(ownedFieldsSet.temporary, ownedFieldsSet.primary),
        None
      )
    }

    def resolveRemovalPredicate(
        pred: Predicate,
        args: List[Expression],
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val defn = resolvePredicateDefinition(
        pred,
        predicates.removal,
        CheckRuntime.Names.removePrefix,
        removeFieldAccess,
        structIdFields,
        resolveRemovalPredicate
      )
      new Invoke(
        defn,
        args ++ List(ownedFieldsSet.temporary, ownedFieldsSet.primary),
        None
      )
    }

    def addFieldAccess(
        member: FieldMember,
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val struct = member.field.struct
      val instanceId =
        new FieldMember(member.root, structIdFields(struct.name))
      val fieldIndex = new Int(struct.fields.indexOf(member.field))
      val numFields = new Int(struct.fields.length)
      new Invoke(
        runtime.addAcc,
        List(
          ownedFieldsSet.primary,
          instanceId,
          numFields,
          fieldIndex
        ),
        None
      )
    }

    def removeFieldAccess(
        member: FieldMember,
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val struct = member.field.struct
      val instanceId = new FieldMember(member.root, structIdFields(struct.name))
      val fieldIndex = new Int(struct.fields.indexOf(member.field))
      new Invoke(
        runtime.loseAcc,
        List(
          ownedFieldsSet.primary,
          instanceId,
          fieldIndex
        ),
        None
      )
    }

    def assertFieldAccess(
        member: FieldMember,
        ownedFieldsSet: OwnedFieldsSet,
        structIdFields: StructIDTracker
    ): Invoke = {
      val struct = member.field.struct
      val instanceId = new FieldMember(member.root, structIdFields(struct.name))
      val fieldIndex = new Int(struct.fields.indexOf(member.field))
      new Invoke(
        runtime.assertAcc,
        List(
          ownedFieldsSet.temporary,
          ownedFieldsSet.primary,
          instanceId,
          fieldIndex,
          //TODO: add support for GraphPrinter.printExpr here
          new String(
            "Field access runtime check failed for struct " + member.field.struct.name + "." + member.field.name
          )
        ),
        None
      )
    }

    def removePermissionsFromContract(
        contract: Option[IRGraph.Expression],
        ownedFieldsTarget: Var,
        structIdFields: Map[scala.Predef.String, StructField]
    ): List[Op] = {
      contract.toList.flatMap(
        translateSpec(
          _,
          removeFieldAccess,
          OwnedFieldsSet(ownedFieldsTarget, new IRGraph.Null()),
          structIdFields,
          resolveRemovalPredicate
        )
      )
    }

    def addPermissionsFromContract(
        contract: Option[IRGraph.Expression],
        ownedFieldsTarget: Expression,
        structIdFields: StructIDTracker
    ): List[Op] = {
      contract.toList.flatMap(
        translateSpec(
          _,
          addFieldAccess,
          OwnedFieldsSet(ownedFieldsTarget, new IRGraph.Null()),
          structIdFields,
          resolveAdditionPredicate
        )
      )
    }

    def translateSpec(
        expr: IRGraph.Expression,
        permissionHandler: PermissionHandler,
        ownedFields: OwnedFieldsSet,
        structIdFields: StructIDTracker,
        predicateHandler: PredicateHandler
    ): Seq[Op] = {
      expr match {
        case accessibility: IRGraph.Accessibility =>
          accessibility.member match {
            case member: FieldMember =>
              Seq(
                permissionHandler(member, ownedFields, structIdFields)
              )
            case _ =>
              throw new WeaverException("Invalid conjunct in specification.")
          }

        case instance: PredicateInstance =>
          Seq(
            predicateHandler(
              instance.predicate,
              instance.arguments,
              ownedFields,
              structIdFields
            )
          )
        case imp: IRGraph.Imprecise =>
          if (imp.precise.isDefined) {
            translateSpec(
              imp.precise.get,
              permissionHandler,
              ownedFields,
              structIdFields,
              predicateHandler
            )
          } else {
            Seq.empty
          }
        case conditional: IRGraph.Conditional => {
          val trueOps =
            translateSpec(
              conditional.ifTrue,
              permissionHandler,
              ownedFields,
              structIdFields,
              predicateHandler
            ).toList
          val falseOps =
            translateSpec(
              conditional.ifFalse,
              permissionHandler,
              ownedFields,
              structIdFields,
              predicateHandler
            ).toList

          if (trueOps.nonEmpty || falseOps.nonEmpty) {
            val ifStmt = new If(conditional.condition)
            ifStmt.ifTrue ++= trueOps
            ifStmt.ifFalse ++= falseOps
            Seq(ifStmt)
          } else {
            Seq.empty
          }
        }

        case binary: Binary if binary.operator == BinaryOp.And =>
          translateSpec(
            binary.left,
            permissionHandler,
            ownedFields,
            structIdFields,
            predicateHandler
          ) ++
            translateSpec(
              binary.right,
              permissionHandler,
              ownedFields,
              structIdFields,
              predicateHandler
            )
        case expr =>
          Seq(new IRGraph.Assert(expr, IRGraph.AssertKind.Imperative))
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
            // Convert precondition into calls to addAcc
            call.ir.insertBefore(
              // TODO
              removePermissionsFromContract(
                callee.precondition,
                getPrimaryOwnedFields,
                structIdFields
              )
            )

            // Convert postcondition into calls to addAcc
            call.ir.insertAfter(
              addPermissionsFromContract(
                callee.postcondition,
                getPrimaryOwnedFields,
                structIdFields
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
          call.ir.insertBefore(
            new Invoke(
              runtime.initOwnedFields,
              List(instanceCounter),
              Some(tempSet)
            ) :: addPermissionsFromContract(
              callee.precondition,
              tempSet,
              structIdFields
            ) ++ removePermissionsFromContract(
              callee.precondition,
              getPrimaryOwnedFields,
              structIdFields
            )
          )

          call.ir.arguments :+= tempSet

          call.ir.insertAfter(
            new Invoke(runtime.join, List(getPrimaryOwnedFields, tempSet), None)
          )
        }
      }
    }

    // If a primary owned fields instance is required for this method, add all allocations into it
    for (ownedFields <- primaryOwnedFields)
      for (alloc <- methodData.allocations) {
        alloc match {
          case alloc: AllocStruct => {
            val structType = alloc.struct
            alloc.insertAfter(
              new Invoke(
                runtime.addStructAcc,
                List(ownedFields, new Int(structType.fields.length - 1)),
                Some(
                  new FieldMember(
                    alloc.target,
                    structIdFields(alloc.struct.name)
                  )
                )
              )
            )
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
