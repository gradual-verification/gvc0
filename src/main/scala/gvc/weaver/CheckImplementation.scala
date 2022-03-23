package gvc.weaver

import gvc.transformer.IRGraph.Expression

import scala.collection.mutable
import gvc.transformer.{Replacer, IRGraph => IR}

sealed trait CheckMode { def prefix: String }
case object AddMode extends CheckMode { def prefix = "add_" }
case object RemoveMode extends CheckMode { def prefix = "remove_" }
case object SeparationMode extends CheckMode { def prefix = "sep_" }
case object VerifyMode extends CheckMode { def prefix = "" }

sealed trait CheckType
case object Separation extends CheckType
case object Verification extends CheckType
class ContextConverter(call: IR.Invoke, caller: IR.Method) {
  val variableMapping =
    (call.callee.parameters zip call.arguments).toMap
  val resultExpression: Option[Expression] =
    if (call.target.isDefined)
      call.target
    else
      call.callee.returnType match {
        case Some(value) =>
          call.target = Some(caller.addVar(value))
          call.target
        case None => None
      }
  def convertExpression(expr: Expression): IR.Expression = {
    expr match {
      case value: IR.Var =>
        value match {
          case parameter: IR.Parameter => variableMapping(parameter)
          case _                       => value
        }
      case fieldMember: IR.FieldMember =>
        new IR.FieldMember(
          convertExpression(fieldMember.root),
          fieldMember.field
        )
      case derefMember: IR.DereferenceMember =>
        new IR.DereferenceMember(convertExpression(derefMember.root))

      case _: IR.Result => resultExpression.get

      case literal: IR.Literal => literal
      case binary: IR.Binary =>
        new IR.Binary(
          binary.operator,
          convertExpression(binary.left),
          convertExpression(binary.right)
        )
      case unary: IR.Unary =>
        new IR.Unary(unary.operator, convertExpression(unary.operand))
      case _ =>
        throw new WeaverException(
          "Invalid expression; cannot convert to new context."
        )
    }
  }
}

class CheckImplementation(
    program: IR.Program,
    runtime: CheckRuntime,
    structIds: Map[String, IR.StructField]
) {
  private val predicateImplementations =
    mutable.Map[(CheckMode, String), Option[IR.MethodDefinition]]()

  private def resolvePredicateDefinition(
      mode: CheckMode,
      pred: IR.Predicate
  ): Option[IR.MethodDefinition] = {

    predicateImplementations.getOrElse(
      (mode, pred.name),
      implementPredicate(mode, pred)
    )
  }

  private def implementPredicate(
      mode: CheckMode,
      pred: IR.Predicate
  ): Option[IR.MethodDefinition] = {

    // TODO: allow name collisions when adding methods
    val defn = program.addMethod(mode.prefix + pred.name, None)
    predicateImplementations += ((mode, pred.name) -> Some(defn))

    val newParams = pred.parameters
      .map((p: IR.Var) => p -> defn.addParameter(p.varType, p.name))
      .toMap

    val perms = defn.addParameter(
      runtime.ownedFieldsRef,
      CheckRuntime.Names.primaryOwnedFields
    )

    // Replace parameters from the predicate definition with parameters
    // in this predicate instance
    val body = Replacer.replace(pred.expression, newParams)

    val ops = translate(mode, body, perms)
    if (ops.nonEmpty) {
      defn.body ++= ops
      Some(defn)
    } else {
      // Otherwise, this predicate implementation is a no-op, and it can be ignored
      // TODO: Remove the no-op method definition
      predicateImplementations.update((mode, pred.name), None)
      None
    }
  }

  def structIdField(struct: IR.StructDefinition) = structIds(struct.name)

  def translate(
      mode: CheckMode,
      expr: IR.Expression,
      perms: IR.Var,
      converter: Option[ContextConverter] = None
  ): Seq[IR.Op] = expr match {
    case acc: IR.Accessibility =>
      acc.member match {
        case member: IR.FieldMember =>
          translateFieldPermission(mode, member, perms, converter)
        case _ =>
          throw new WeaverException("Invalid conjunct in specification.")
      }
    case pred: IR.PredicateInstance =>
      translatePredicateInstance(mode, pred, perms, converter)

    case imp: IR.Imprecise =>
      imp.precise match {
        case None          => Seq.empty
        case Some(precise) => translate(mode, precise, perms, converter)
      }

    case conditional: IR.Conditional => {
      val trueOps = translate(mode, conditional.ifTrue, perms, converter)
      val falseOps = translate(mode, conditional.ifFalse, perms, converter)
      val condition =
        if (converter.isDefined)
          converter.get.convertExpression(conditional.condition)
        else conditional.condition
      (trueOps.isEmpty, falseOps.isEmpty) match {
        case (false, false) => {
          val ifStmt = new IR.If(condition)
          ifStmt.ifTrue ++= trueOps
          ifStmt.ifFalse ++= falseOps
          Seq(ifStmt)
        }
        case (false, true) => {
          val ifStmt = new IR.If(condition)
          ifStmt.ifTrue ++= trueOps
          Seq(ifStmt)
        }
        case (true, false) => {
          val ifStmt =
            new IR.If(new IR.Unary(IR.UnaryOp.Not, condition))
          ifStmt.ifTrue ++= falseOps
          Seq(ifStmt)
        }
        case (true, true) => {
          Seq.empty
        }
      }
    }

    case binary: IR.Binary if binary.operator == IR.BinaryOp.And => {
      translate(mode, binary.left, perms, converter) ++ translate(
        mode,
        binary.right,
        perms,
        converter
      )
    }

    case expr =>
      mode match {
        case SeparationMode | AddMode | RemoveMode => Seq.empty
        case VerifyMode => {
          val toAssert =
            if (converter.isDefined) converter.get.convertExpression(expr)
            else expr
          Seq(new IR.Assert(toAssert, IR.AssertKind.Imperative))
        }
      }
  }

  def translateFieldPermission(
      mode: CheckMode,
      member: IR.FieldMember,
      perms: IR.Var,
      contextConverter: Option[ContextConverter] = None
  ): Seq[IR.Op] = {

    val convertedMember =
      if (contextConverter.isDefined)
        contextConverter.get
          .convertExpression(member)
          .asInstanceOf[IR.FieldMember]
      else member
    val struct = convertedMember.field.struct
    val instanceId =
      new IR.FieldMember(convertedMember.root, structIdField(struct))
    val fieldIndex = new IR.Int(struct.fields.indexOf(convertedMember.field))
    val numFields = new IR.Int(struct.fields.length)
    //TODO: add support for GraphPrinter.printExpr here
    val fullName = s"struct ${struct.name}.${convertedMember.field.name}"

    mode match {
      case SeparationMode =>
        val error =
          new IR.String(s"Overlapping field permissions for $fullName")
        Seq(
          new IR.Invoke(
            runtime.addAccEnsureSeparate,
            List(perms, instanceId, fieldIndex, numFields, error),
            None
          )
        )
      case VerifyMode =>
        val error =
          new IR.String(s"Field access runtime check failed for $fullName")
        Seq(
          new IR.Invoke(
            runtime.assertAcc,
            List(perms, instanceId, fieldIndex, error),
            None
          )
        )
      case RemoveMode =>
        Seq(
          new IR.Invoke(
            runtime.loseAcc,
            List(perms, instanceId, fieldIndex),
            None
          )
        )

      // TODO: We need to also add permissions required for framing
      case AddMode =>
        Seq(
          new IR.Invoke(
            runtime.addAcc,
            List(perms, instanceId, numFields, fieldIndex),
            None
          )
        )
    }
  }

  def translatePredicateInstance(
      mode: CheckMode,
      pred: IR.PredicateInstance,
      perms: IR.Var,
      converter: Option[ContextConverter] = None
  ): Seq[IR.Op] = {
    val arguments =
      if (converter.isDefined)
        pred.arguments.map(converter.get.convertExpression)
      else pred.arguments
    resolvePredicateDefinition(mode, pred.predicate)
      .map(new IR.Invoke(_, arguments :+ perms, None))
      .toSeq
  }

}
