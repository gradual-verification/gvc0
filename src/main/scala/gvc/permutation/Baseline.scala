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
import gvc.weaver.Checker.{CheckContext, addAllocationTracking, implementChecks}
import gvc.weaver.Collector.{CheckInfo, ImmediateCondition, resolveValue}
import gvc.weaver.{
  CheckExpression,
  CheckImplementation,
  CheckMethod,
  CheckRuntime,
  CheckType,
  FieldAccessibilityCheck,
  FieldPermissionCheck,
  FieldSeparationCheck,
  PermissionCheck,
  PredicateAccessibilityCheck,
  PredicatePermissionCheck,
  PredicateSeparationCheck,
  Separation,
  Verification,
  VerifyMode,
  WeaverException
}

import scala.collection.mutable
import gvc.weaver.ValueContext

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

    program.methods
      .filter(!_.maskedLibrary)
      .map(method =>
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
    val context =
      CheckContext(
        program,
        collected.baseMethod,
        implementation,
        runtime
      )
    val method = collected.baseMethod.method

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

    // If a primary owned fields instance is required for this method, add all allocations into it
    if (collected.allocations.nonEmpty) {
      addAllocationTracking(
        Some(getPrimaryOwnedFields()),
        collected.allocations,
        implementation,
        runtime
      )
    }

    def checkSpec(
        expr: Expression,
        returnValue: Option[Expression] = None
    ): Seq[Op] = {
      val perms = createCheckTree(expr, None, None)
      collectTranslation(perms, returnValue)
    }

    def convertTo(info: CheckInfo, mode: CheckType): CheckInfo = {
      CheckInfo(
        info.check match {
          case perm: PermissionCheck =>
            perm match {
              case field: FieldPermissionCheck =>
                mode match {
                  case Verification =>
                    field match {
                      case FieldSeparationCheck(field) =>
                        FieldAccessibilityCheck(field)
                      case _ => field
                    }
                  case Separation =>
                    field match {
                      case FieldAccessibilityCheck(field) =>
                        FieldSeparationCheck(field)
                      case _ => field
                    }
                }
              case pred: PredicatePermissionCheck =>
                mode match {
                  case Verification =>
                    pred match {
                      case PredicateSeparationCheck(predicateName, arguments) =>
                        PredicateAccessibilityCheck(
                          predicateName,
                          arguments
                        )
                      case _ =>
                        pred
                    }
                  case Separation =>
                    pred match {
                      case PredicateAccessibilityCheck(
                            predicateName,
                            arguments
                          ) =>
                        PredicateSeparationCheck(predicateName, arguments)
                      case _ =>
                        pred
                    }
                }
            }
          case expression: CheckExpression => expression
        },
        info.when
      )
    }
    def collectTranslation(
        node: CheckNode,
        returnValue: Option[Expression] = None,
        separate: Boolean = false
    ): Seq[Op] = {
      val separation = separate || needsSeparation(node)
      val checks: Seq[CheckInfo] =
        (if (separation) {
           node.checksAtLevel
             .filter(
               _.check
                 .isInstanceOf[PermissionCheck]
             )
             .map(convertTo(_, Separation))
         } else {
           Seq()
         }) ++ node.checksAtLevel
      val grouped = checks
        .groupBy(info => info.when)
        .map(entry =>
          (
            if (entry._1.isDefined) entry._1.get match {
              case ImmediateCondition(value) =>
                Some(
                  value.toIR(
                    context.program,
                    collected.baseMethod.asInstanceOf[CheckMethod],
                    returnValue
                  )
                )
              case _ => None
            }
            else None,
            entry._2.map(info => info.check).toList
          )
        )
        .flatMap(irEntry => {
          implementChecks(
            irEntry._1,
            irEntry._2,
            returnValue,
            getPrimaryOwnedFields,
            instanceCounter,
            context
          )
        })
        .toSeq
      grouped ++ node.branches.flatMap(node =>
        collectTranslation(node, returnValue, separate)
      )
    }

    collected.calls
      .filter(!_.callee.asInstanceOf[Method].maskedLibrary)
      .foreach(call => {
        call.arguments = call.arguments ++ List(getPrimaryOwnedFields())
      })

    collected.framing.foreach(framing => {
      framing.op.insertBefore(
        framing.fields.flatMap(
          implementation.translateFieldPermission(
            VerifyMode,
            _,
            getPrimaryOwnedFields(),
            ValueContext
          )
        )
      )
    })

    collected.assertions.foreach(assert => {
      assert.insertBefore(checkSpec(assert.value))
    })

    collected.whileLoops.foreach(whl => {
      if (whl.invariant.isDefined) {
        val check = checkSpec(whl.invariant.get)
        check ++=: whl.body
        whl.insertAfter(check.map(_.copy))
      }
    })

    if (method.precondition.isDefined)
      initializeOps ++= checkSpec(method.precondition.get)

    if (method.postcondition.isDefined) {
      collected.returns.foreach(ret =>
        ret.insertBefore(
          checkSpec(method.postcondition.get, ret.value)
        )
      )
      if (collected.hasImplicitReturn)
        method.body ++= checkSpec(method.postcondition.get, None)
    }

    // Finally, add all the initialization ops to the beginning
    initializeOps ++=: method.body
    method

  }

  def needsSeparation(node: CheckNode): Boolean = {
    val found =
      node.checksAtLevel.find(info => info.check.isInstanceOf[PermissionCheck])
    (found.isDefined && node.checksAtLevel.exists(info =>
      info.check.isInstanceOf[PermissionCheck] && !info.equals(found.get)
    )) || node.branches.exists(node => needsSeparation(node))
  }

  class CheckNode {
    val checksAtLevel: mutable.ListBuffer[CheckInfo] =
      mutable.ListBuffer[CheckInfo]()
    var branches: mutable.ListBuffer[CheckNode] =
      mutable.ListBuffer[CheckNode]()

    def ++(rVal: CheckNode): CheckNode = {
      val combined = new CheckNode()
      combined.checksAtLevel ++= checksAtLevel
      combined.branches = branches ++ rVal.branches
      combined
    }
  }

  def createCheckTree(
      spec: Expression,
      arguments: Option[Map[Parameter, CheckExpression]],
      condition: Option[CheckExpression]
  ): CheckNode = spec match {
    // Imprecise expressions just needs the precise part checked.
    case imp: Imprecise =>
      if (imp.precise.isDefined) {
        createCheckTree(
          imp.precise.get,
          arguments,
          condition
        )
      } else {
        new CheckNode()
      }

    // And expressions just traverses both parts
    case and: Binary if and.operator == BinaryOp.And =>
      val left =
        createCheckTree(and.left, arguments, condition)
      val right =
        createCheckTree(
          and.right,
          arguments,
          condition
        )
      right ++ left

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
      node.branches +=
        createCheckTree(
          cond.ifTrue,
          arguments,
          Some(trueCond)
        )
      node.branches +=
        createCheckTree(
          cond.ifFalse,
          arguments,
          Some(falseCond)
        )
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
      node.checksAtLevel += CheckInfo(
        FieldAccessibilityCheck(field),
        condition.map(ImmediateCondition)
      )
      node
    }
    case pred: PredicateInstance => {
      val node = new CheckNode()
      node.checksAtLevel +=
        CheckInfo(
          PredicateAccessibilityCheck(
            pred.predicate.name,
            pred.arguments.map(CheckExpression.irValue)
          ),
          condition.map(ImmediateCondition)
        )
      node
    }
    case expr: Expression =>
      val node = new CheckNode()
      node.checksAtLevel += CheckInfo(
        CheckExpression.irValue(expr),
        condition.map(ImmediateCondition)
      )
      node
  }
}
