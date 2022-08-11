package gvc.weaver

import gvc.transformer.{IR, SilverVarId}
import Collector._
import scala.collection.mutable
import scala.annotation.tailrec

object Checker {
  type StructIDTracker = Map[String, IR.StructField]

  class CheckerMethod(
      val method: IR.Method,
      tempVars: Map[SilverVarId, IR.Invoke]
  ) extends CheckMethod {
    val resultVars = mutable.Map[String, IR.Expression]()

    def resultVar(name: String): IR.Expression = {
      resultVars.getOrElseUpdate(
        name, {
          val invoke = tempVars.getOrElse(
            SilverVarId(method.name, name),
            throw new WeaverException(s"Missing temporary variable '$name'")
          )

          invoke.target.getOrElse {
            val retType = invoke.method.returnType.getOrElse(
              throw new WeaverException(
                s"Invalid temporary variable '$name' for void '${invoke.callee.name}'"
              )
            )

            val tempVar = method.addVar(retType)
            invoke.target = Some(tempVar)
            tempVar
          }
        }
      )
    }
  }

  def insert(program: Collector.CollectedProgram): Unit = {
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

    val callsImprecise: Boolean = methodData.calls.exists(c =>
      programData.methods.get(c.ir.callee.name) match {
        case Some(value) => value.callStyle != PreciseCallStyle
        case None        => false
    })

    // `ops` is a function that generates the operations, given the current return value at that
    // position. DO NOT construct the ops before passing them to this method since multiple copies
    // may be required.
    def insertAt(at: Location, ops: Option[IR.Expression] => Seq[IR.Op]): Unit =
      at match {
        case LoopStart(op: IR.While) => ops(None) ++=: op.body
        case LoopEnd(op: IR.While)   => op.body ++= ops(None)
        case Pre(op)                 => op.insertBefore(ops(None))
        case Post(op)                => op.insertAfter(ops(None))
        case MethodPre               => ops(None) ++=: method.body
        case MethodPost =>
          methodData.returns.foreach(e => e.insertBefore(ops(e.value)))
          if (methodData.hasImplicitReturn) {
            method.body ++= ops(None)
          }
        case _ => throw new WeaverException(s"Invalid location '$at'")
      }

    var nextConditionalId = 1
    val conditionVars = methodData.conditions.map { c =>
      val flag = method.addVar(IR.BoolType, s"_cond_$nextConditionalId")
      nextConditionalId += 1
      c -> flag
    }.toMap

    def foldConditionList(conds: List[Condition],
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
      case ImmediateCondition(expr) => expr.toIR(program, checkMethod, None)
      case cond: TrackedCondition   => conditionVars(cond)
      case NotCondition(value) =>
        new IR.Unary(IR.UnaryOp.Not, getCondition(value))
      case AndCondition(values) => foldConditionList(values, IR.BinaryOp.And)
      case OrCondition(values)  => foldConditionList(values, IR.BinaryOp.Or)
    }

    val initializeOps = mutable.ListBuffer[IR.Op]()

    def methodContainsImprecision(methodData: CollectedMethod): Boolean = {
      methodData.bodyContainsImprecision ||
      methodData.calls.exists(
        c =>
          c.ir.callee.isInstanceOf[IR.Method] &&
            (programData.methods(c.ir.callee.name).callStyle match {
              case ImpreciseCallStyle | PrecisePreCallStyle => true
              case _                                        => false
            })
      )
    }

    var (primaryOwnedFields, instanceCounter) = methodData.callStyle match {
      case MainCallStyle => {
        val instanceCounter =
          method.addVar(
            new IR.PointerType(IR.IntType),
            CheckRuntime.Names.instanceCounter
          )
        initializeOps += new IR.AllocValue(IR.IntType, instanceCounter)
        (None, instanceCounter)
      }

      case PreciseCallStyle => {
        if (methodContainsImprecision(methodData)) {
          val ownedFields: IR.Var = method.addParameter(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.primaryOwnedFields)
          val instanceCounter =
            new IR.FieldMember(ownedFields, runtime.ownedFieldInstanceCounter)
          (Some(ownedFields), instanceCounter)
        } else {
          val instanceCounter =
            method.addParameter(
              new IR.PointerType(IR.IntType),
              CheckRuntime.Names.instanceCounter
            )
          (None, instanceCounter)
        }
      }

      case ImpreciseCallStyle | PrecisePreCallStyle => {
        val ownedFields: IR.Var =
          method.addParameter(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.primaryOwnedFields
          )
        val instanceCounter =
          new IR.FieldMember(ownedFields, runtime.ownedFieldInstanceCounter)
        (Some(ownedFields), instanceCounter)
      }
    }

    def getPrimaryOwnedFields(): IR.Var = primaryOwnedFields.getOrElse {
      val ownedFields = method.addVar(
        runtime.ownedFieldsRef,
        CheckRuntime.Names.primaryOwnedFields
      )
      primaryOwnedFields = Some(ownedFields)

      initializeOps += new IR.Invoke(
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
    for ((loc, checkData) <- groupChecks(methodData.checks)) {
      insertAt(
        loc,
        retVal => {
          val ops = mutable.ListBuffer[IR.Op]()

          // Create a temporary owned fields instance when it is required
          var temporaryOwnedFields: Option[IR.Var] = None

          def getTemporaryOwnedFields(): IR.Var =
            temporaryOwnedFields.getOrElse {
              val tempVar = context.method.method.addVar(
                context.runtime.ownedFieldsRef,
                CheckRuntime.Names.temporaryOwnedFields
              )
              temporaryOwnedFields = Some(tempVar)
              tempVar
            }

          for ((cond, checks) <- checkData) {
            val condition = cond.map(getCondition(_))
            ops ++= implementChecks(
              condition,
              checks.map(_.check),
              retVal,
              getPrimaryOwnedFields,
              getTemporaryOwnedFields,
              instanceCounter,
              context
            )
          }

          // Prepend op to initialize owned fields if it is required
          temporaryOwnedFields.foreach { tempOwned =>
            new IR.Invoke(
              context.runtime.initOwnedFields,
              List(instanceCounter),
              Some(tempOwned)
            ) +=: ops
          }

          ops
        }
      )
    }

    val needsToTrackPrecisePerms = methodContainsImprecision(methodData)

    if (needsToTrackPrecisePerms && methodData.callStyle == PreciseCallStyle) {
      primaryOwnedFields match {
        case Some(_) =>
          initializeOps ++= methodData.method.precondition.toSeq.flatMap(
            implementation.translate(
              AddMode,
              _,
              getPrimaryOwnedFields,
              None,
              ValueContext
            )
          )
        case None =>
      }
    }
    // Update the call sites to add any required parameters
    for (call <- methodData.calls) {
      call.ir.callee match {
        case _: IR.DependencyMethod => ()
        case callee: IR.Method =>
          val calleeData = programData.methods(callee.name)
          calleeData.callStyle match {
            // No parameters can be added to a main method
            case MainCallStyle => ()

            // Imprecise methods always get the primary owned fields instance directly
            case ImpreciseCallStyle =>
              call.ir.arguments :+= getPrimaryOwnedFields()

            case PreciseCallStyle => {
              val context = new CallSiteContext(call.ir, method)

              if (methodContainsImprecision(calleeData)) {
                val tempSet = method.addVar(
                  runtime.ownedFieldsRef,
                  CheckRuntime.Names.temporaryOwnedFields
                )
                call.ir.arguments :+= tempSet

                val initTemp = new IR.Invoke(
                  runtime.initOwnedFields,
                  List(instanceCounter),
                  Some(tempSet)
                )

                call.ir.insertBefore(initTemp)
                if (needsToTrackPrecisePerms) {
                  call.ir.insertBefore(
                    callee.precondition.toSeq
                      .flatMap(
                        implementation
                          .translate(AddRemoveMode,
                                     _,
                                     tempSet,
                                     Some(getPrimaryOwnedFields()),
                                     context)
                      )
                      .toList
                  )
                }
              } else {
                call.ir.arguments :+= instanceCounter
                if (needsToTrackPrecisePerms) {
                  val removePermsPrior = callee.precondition.toSeq
                    .flatMap(
                      implementation
                        .translate(RemoveMode,
                                   _,
                                   getPrimaryOwnedFields(),
                                   None,
                                   context)
                    )
                    .toList
                  call.ir.insertBefore(removePermsPrior)
                }
              }
              if (needsToTrackPrecisePerms) {
                val addPermsAfter = callee.postcondition.toSeq
                  .flatMap(
                    implementation
                      .translate(AddMode,
                                 _,
                                 getPrimaryOwnedFields(),
                                 None,
                                 context)
                  )
                  .toList
                call.ir.insertAfter(addPermsAfter)
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

              val createTemp = new IR.Invoke(
                runtime.initOwnedFields,
                List(instanceCounter),
                Some(tempSet)
              )

              val context = new CallSiteContext(call.ir, method)

              val resolvePermissions = callee.precondition.toSeq
                .flatMap(
                  implementation.translate(AddRemoveMode,
                                           _,
                                           tempSet,
                                           Some(getPrimaryOwnedFields),
                                           context)
                )
                .toList
              call.ir.insertBefore(
                createTemp :: resolvePermissions
              )
              call.ir.arguments :+= tempSet
              call.ir.insertAfter(
                new IR.Invoke(
                  runtime.join,
                  List(getPrimaryOwnedFields, tempSet),
                  None
                )
              )
            }
          }
      }
    }

    // If a primary owned fields instance is required for this method, add all allocations into it
    addAllocationTracking(
      primaryOwnedFields,
      instanceCounter,
      methodData.allocations,
      implementation,
      runtime
    )

    // Add all conditions that need tracked
    // Group all conditions for a single location and insert in sequence
    // to preserve the correct ordering of conditions.
    methodData.conditions
      .groupBy(_.location)
      .foreach {
        case (loc, conds) =>
          insertAt(loc, retVal => {
            conds.map(
              c =>
                new IR.Assign(conditionVars(c),
                              c.value.toIR(program, checkMethod, retVal)))
          })
      }

    // Finally, add all the initialization ops to the beginning
    initializeOps ++=: method.body
  }

  def addAllocationTracking(
      primaryOwnedFields: Option[IR.Var],
      instanceCounter: IR.Expression,
      allocations: List[IR.Op],
      implementation: CheckImplementation,
      runtime: CheckRuntime
  ): Unit = {
    for (alloc <- allocations) {
      alloc match {
        case alloc: IR.AllocStruct =>
          primaryOwnedFields match {
            case Some(primary) => implementation.trackAllocation(alloc, primary)
            case None          => implementation.idAllocation(alloc, instanceCounter)
          }
        case _ =>
          throw new WeaverException(
            "Tracking is only currently supported for struct allocations."
          )
      }
    }
  }

  def implementAccCheck(
      check: FieldPermissionCheck,
      fields: FieldCollection,
      context: CheckContext
  ): Seq[IR.Op] = {
    val field = check.field.toIR(context.program, context.method, None)
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
      primaryOwnedFields: () => IR.Var,
      temporaryOwnedFields: () => IR.Var
  )

  case class CheckContext(
      program: IR.Program,
      method: CheckMethod,
      implementation: CheckImplementation,
      runtime: CheckRuntime
  )

  def implementCheck(
      check: Check,
      returnValue: Option[IR.Expression],
      fields: FieldCollection,
      context: CheckContext
  ): Seq[IR.Op] = {
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
      getPrimaryOwnedFields: () => IR.Var,
      getTemporaryOwnedFields: () => IR.Var,
      instanceCounter: IR.Expression,
      context: CheckContext
  ): Seq[IR.Op] = {
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

  def groupChecks(items: List[RuntimeCheck])
    : List[(Location, List[(Option[Condition], List[RuntimeCheck])])] = {
    items
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
        CheckExpression.Result | _: CheckExpression.ResultVar =>
      1
  }
}
