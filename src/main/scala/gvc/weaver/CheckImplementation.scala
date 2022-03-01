package gvc.weaver

import scala.collection.mutable
import gvc.transformer.{IRGraph => IR}
import gvc.transformer.Replacer

sealed trait CheckMode { def prefix: String }
case object AddMode extends CheckMode { def prefix = "add_" }
case object RemoveMode extends CheckMode { def prefix = "remove_" }
case object SeparationMode extends CheckMode { def prefix = "sep_"}
case object VerifyMode extends CheckMode { def prefix = "" }

class CheckImplementation(
  program: IR.Program,
  runtime: CheckRuntime,
  structIds: Map[String, IR.StructField],
) {
  private val predicateImplementations = mutable.Map[(CheckMode, IR.Predicate), Option[IR.MethodDefinition]]()

  private def resolvePredicateDefinition(mode: CheckMode, pred: IR.Predicate): Option[IR.MethodDefinition] = {
    predicateImplementations.getOrElse((mode, pred), implementPredicate(mode, pred))
  }

  private def implementPredicate(mode: CheckMode, pred: IR.Predicate): Option[IR.MethodDefinition] = {
    // TODO: allow name collisions when adding methods
    val defn = program.addMethod(mode.prefix + pred.name, None)
    predicateImplementations += (mode, pred) -> Some(defn)

    val newParams = pred.parameters.map((p: IR.Var) =>
      p -> defn.addParameter(p.varType, p.name)
    ).toMap

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
      predicateImplementations.update((mode, pred), None)
      None
    }
  }

  def structIdField(struct: IR.StructDefinition) = structIds(struct.name)

  def translate(mode: CheckMode, expr: IR.Expression, perms: IR.Var): Seq[IR.Op] = expr match {
    case acc: IR.Accessibility =>
      acc.member match {
        case member: IR.FieldMember =>
          translateFieldPermission(mode, member, perms)
        case _ =>
          throw new WeaverException("Invalid conjunct in specification.")
      }

      case pred: IR.PredicateInstance =>
        translatePredicateInstance(mode, pred, perms)

      case imp: IR.Imprecise => imp.precise match {
        case None => Seq.empty
        case Some(precise) => translate(mode, precise, perms)
      }
      
      case conditional: IR.Conditional => {
        val trueOps = translate(mode, conditional.ifTrue, perms)
        val falseOps = translate(mode, conditional.ifFalse, perms)
        
        (trueOps.isEmpty, falseOps.isEmpty) match {
          case (false, false) => {
            val ifStmt = new IR.If(conditional.condition)
            ifStmt.ifTrue ++= trueOps
            ifStmt.ifFalse ++= falseOps
            Seq(ifStmt)
          }
          case (false, true) => {
            val ifStmt = new IR.If(conditional.condition)
            ifStmt.ifTrue ++= trueOps
            Seq(ifStmt)
          }
          case (true, false) => {
            val ifStmt = new IR.If(new IR.Unary(IR.UnaryOp.Not, conditional.condition))
            ifStmt.ifTrue ++= falseOps
            Seq(ifStmt)
          }
          case (true, true) => {
            Seq.empty
          }
        }
      }

      case binary: IR.Binary if binary.operator == IR.BinaryOp.And => {
        translate(mode, binary.left, perms) ++ translate(mode, binary.right, perms)
      }

      case expr => mode match {
        case SeparationMode | AddMode | RemoveMode => Seq.empty
        case VerifyMode => Seq(new IR.Assert(expr, IR.AssertKind.Imperative))
      }
  }

  def translateFieldPermission(
    mode: CheckMode,
    member: IR.FieldMember,
    perms: IR.Var
  ): Seq[IR.Op] = {
    val struct = member.field.struct
    val instanceId = new IR.FieldMember(member.root, structIdField(struct))
    val fieldIndex = new IR.Int(struct.fields.indexOf(member.field))
    val numFields = new IR.Int(struct.fields.length)
    //TODO: add support for GraphPrinter.printExpr here
    val fullName = s"struct ${struct.name}.${member.field.name}"

    mode match {
      case SeparationMode =>
        val error = new IR.String(s"Overlapping field permissions for $fullName")
        Seq(new IR.Invoke(
          runtime.addAccEnsureSeparate,
          List(perms, instanceId, fieldIndex, numFields, error),
          None
        ))
      case VerifyMode =>
        val error = new IR.String(s"Field access runtime check failed for $fullName")
        Seq(new IR.Invoke(
          runtime.assertAcc,
          List(perms, instanceId, fieldIndex, error),
          None
        ))
      case RemoveMode =>
        Seq(new IR.Invoke(runtime.loseAcc, List(perms, instanceId, fieldIndex), None))
      
      // TODO: We need to also add permissions required for framing
      case AddMode =>
        Seq(new IR.Invoke(
          runtime.addAcc,
          List(perms, instanceId, fieldIndex, numFields),
          None
        ))
    }
  }

  def translatePredicateInstance(mode: CheckMode, pred: IR.PredicateInstance, perms: IR.Var): Seq[IR.Op] = {
    resolvePredicateDefinition(mode, pred.predicate)
      .map(new IR.Invoke(_, pred.arguments :+ perms, None))
      .toSeq
  }
}