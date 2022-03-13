package gvc.permutation

import gvc.permutation.BaselineCollector.BaselineCollectedMethod
import gvc.transformer.IRGraph.{
  Accessibility,
  AllocValue,
  Binary,
  BinaryOp,
  Conditional,
  Expression,
  FieldMember,
  Imprecise,
  IntType,
  Invoke,
  Method,
  Op,
  Parameter,
  PointerType,
  PredicateInstance,
  Program,
  Var
}
import gvc.weaver.Checker.addAllocationTracking
import gvc.weaver.Collector.{
  CheckInfo,
  ConditionValue,
  resolveValue,
  traversePermissions
}
import gvc.weaver.{
  CheckExpression,
  CheckImplementation,
  CheckRuntime,
  FieldAccessibilityCheck,
  PredicateAccessibilityCheck,
  PredicatePermissionCheck,
  PredicateSeparationCheck,
  SeparationMode,
  VerifyMode,
  WeaverException
}

import scala.collection.mutable

object Baseline {

  def insert(program: Program): Unit = {
    val runtime = CheckRuntime.addToIR(program)
    val collectedMethods = BaselineCollector.collect(program)

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance

    val structIdFields = program.structs
      .map(s => (s.name, s.addField(CheckRuntime.Names.id, IntType)))
      .toMap

    val implementation =
      new CheckImplementation(program, runtime, structIdFields)

    program.methods.map(method =>
      insert(
        program,
        collectedMethods(method.name),
        runtime,
        implementation
      )
    )
  }

  private def insert(
      program: Program,
      collected: BaselineCollectedMethod,
      runtime: CheckRuntime,
      implementation: CheckImplementation
  ): Method = {

    val initializeOps = mutable.ListBuffer[Op]()
    val method = collected.method

    var (primaryOwnedFields, instanceCounter) = method.name match {
      case "main" =>
        val instanceCounter =
          method.addVar(
            new PointerType(IntType),
            CheckRuntime.Names.instanceCounter
          )
        initializeOps += new AllocValue(IntType, instanceCounter)
        (None, instanceCounter)

      case _ =>
        val ownedFields: Var =
          method.addParameter(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.primaryOwnedFields
          )
        val instanceCounter =
          new FieldMember(ownedFields, runtime.ownedFieldInstanceCounter)
        (Some(ownedFields), instanceCounter)
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

    // If a primary owned fields instance is required for this method, add all allocations into it
    addAllocationTracking(
      primaryOwnedFields,
      collected.allocations,
      implementation,
      runtime
    )

    def checkSpec(
        ir: Program,
        expr: Expression,
        returnValue: Option[Expression] = None
    ): Seq[Op] = {
      val temporaryOwnedFields = method.addVar(
        runtime.ownedFieldsRef,
        CheckRuntime.Names.temporaryOwnedFields
      )

      val collectedChecks = createCheckTree(expr, None, None)

      /*val irChecks = collectedChecks.map(info =>
        info.check match {
          case check: PermissionCheck =>
            check match {
              case check: FieldPermissionCheck =>
                new Accessibility(check.field.toIR(ir, method, returnValue))
              case check: PredicatePermissionCheck =>
                new PredicateInstance(
                  ir.predicate(check.predicateName),
                  check.arguments.map(_.toIR(ir, method, returnValue))
                )
            }
          case expression: CheckExpression =>
            expression.toIR(ir, method, returnValue)
        }
      )*/
      Seq()
    }

    collected.calls.foreach(call => {
      call.arguments = call.arguments ++ List(getPrimaryOwnedFields)
    })

    collected.framing.foreach(framing => {
      framing.op.insertBefore(
        framing.fields.flatMap(
          implementation.translateFieldPermission(
            VerifyMode,
            _,
            getPrimaryOwnedFields
          )
        )
      )
    })

    collected.assertions.foreach(assert => {
      assert.insertBefore(checkSpec(program, assert.value))
    })

    collected.whileLoops.foreach(whl => {
      if (whl.invariant.isDefined) {
        val check = checkSpec(program, whl.invariant.get)
        check ++=: whl.body
        whl.insertAfter(check.map(_.copy))
      }
    })

    if (method.precondition.isDefined)
      initializeOps ++= checkSpec(program, method.precondition.get)

    if (method.postcondition.isDefined) {
      collected.returns.foreach(ret =>
        ret.insertBefore(
          checkSpec(program, method.postcondition.get, ret.value)
        )
      )
      if (collected.hasImplicitReturn)
        method.body ++= checkSpec(program, method.postcondition.get, None)
    }

    // Finally, add all the initialization ops to the beginning
    initializeOps ++=: method.body
    method
  }

  class CheckCollection(
      basic: Seq[CheckInfo] = Seq(),
      field: Seq[CheckInfo] = Seq()
  ) {
    val basicChecks = basic
    val fieldChecks = field
    def ++(rVal: CheckCollection): CheckCollection = {
      new CheckCollection(
        basicChecks ++ rVal.basicChecks,
        fieldChecks ++ rVal.fieldChecks
      )
    }
  }

  class CheckNode {
    val checksAtLevel = mutable.ListBuffer[CheckInfo]()
    var branches: mutable.Map[CheckExpression, CheckNode] =
      mutable.Map[CheckExpression, CheckNode]()
    var containsFieldChecks = false
    def ++(rVal: CheckNode): CheckNode = {
      val combined = new CheckNode()
      combined.checksAtLevel ++= checksAtLevel
      combined.branches = branches
      rVal.branches.keys.foreach(key =>
        if (combined.branches.contains(key)) {
          combined.branches += key -> combined
            .branches(key)
            .++(rVal.branches(key))
        } else {
          combined.branches += (key -> rVal.branches(key))
        }
      )
      combined.containsFieldChecks =
        containsFieldChecks || rVal.containsFieldChecks

      combined
    }
  }
  def createCheckTree(
      spec: Expression,
      arguments: Option[Map[Parameter, CheckExpression]],
      condition: Option[CheckExpression]
  ): CheckNode = spec match {
    // Imprecise expressions just needs the precise part checked.
    case imp: Imprecise => {
      if (imp.precise.isDefined) {
        createCheckTree(
          imp.precise.get,
          arguments,
          condition
        )
      } else {
        new CheckNode()
      }
    }

    // And expressions just traverses both parts
    case and: Binary if and.operator == BinaryOp.And => {
      val left =
        createCheckTree(and.left, arguments, condition)
      val right =
        createCheckTree(
          and.right,
          arguments,
          condition
        )
      right ++ left
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
      val node = new CheckNode()
      node.branches += (trueCond ->
        createCheckTree(
          cond.ifTrue,
          arguments,
          Some(trueCond)
        ))
      node.branches += (falseCond ->
        createCheckTree(
          cond.ifFalse,
          arguments,
          Some(falseCond)
        ))
      node
    }
    // A single accessibility check
    case acc: Accessibility => {
      val field = resolveValue(acc.member, arguments) match {
        case f: CheckExpression.Field => f
        case invalid =>
          throw new WeaverException(s"Invalid acc() argument: '$invalid'")
      }

      val node = new CheckNode()
      node.containsFieldChecks = true
      node.checksAtLevel += CheckInfo(
        FieldAccessibilityCheck(field),
        condition.map(ConditionValue)
      )
      node
    }
    case pred: PredicateInstance => {
      val node = new CheckNode()
      node.containsFieldChecks = true
      node.checksAtLevel +=
        CheckInfo(
          PredicateAccessibilityCheck(
            pred.predicate.name,
            pred.arguments.map(CheckExpression.irValue)
          ),
          condition.map(ConditionValue)
        )
      node
    }
    case expr: Expression =>
      val node = new CheckNode()
      node.checksAtLevel += CheckInfo(
        CheckExpression.irValue(expr),
        condition.map(ConditionValue)
      )
      node
  }
}
