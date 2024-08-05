package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR
import gvc.transformer.IRPrinter

sealed trait CheckMode {
  def prefix: String
  def perms: IR.Expression
  def withPerms(perms: IR.Expression): CheckMode
  def guarded: Boolean

  def visitPerm(
    runtime: CheckRuntime,
    instanceId: IR.Expression,
    fieldIndex: IR.Expression,
    numFields: IR.Expression,
    expression: String
  ): Seq[IR.Op]

  def visitBool(
    runtime: CheckRuntime,
    value: IR.Expression
  ): Seq[IR.Op]
}

case class AssertMode(val perms: IR.Expression) extends CheckMode {
  def prefix = "assert_"
  def withPerms(perms: IR.Expression): CheckMode = AssertMode(perms)
  def guarded = true

  def visitPerm(
    runtime: CheckRuntime,
    instanceId: IR.Expression,
    fieldIndex: IR.Expression,
    numFields: IR.Expression,
    expression: String
  ): Seq[IR.Op] = {
    val error = new IR.StringLit(s"No permission to access '$expression'")
    val args = List(perms, instanceId, fieldIndex, error)
    val invoke = new IR.Invoke(runtime.assert, args, None)
    Seq(invoke)
  }

  def visitBool(runtime: CheckRuntime, value: IR.Expression): Seq[IR.Op] = {
    val assert = new IR.Assert(value, IR.AssertKind.Imperative)
    Seq(assert)
  }
}
case class AddMode(val perms: IR.Expression, val guarded: Boolean = true) extends CheckMode {
  def prefix = "add_"
  def withPerms(perms: IR.Expression): CheckMode = AddMode(perms)

  def visitPerm(runtime: CheckRuntime, instanceId: IR.Expression, fieldIndex: IR.Expression, numFields: IR.Expression, expression: String): Seq[IR.Op] = {
    // TODO (?): We need to also add permissions required for framing
    val error = new IR.StringLit(s"Invalid aliasing - '$expression' overlaps with existing permission")
    val args = List(perms, instanceId, numFields, fieldIndex, error)
    val invoke = new IR.Invoke(runtime.add, args, None)
    Seq(invoke)
  }

  def visitBool(runtime: CheckRuntime, value: IR.Expression): Seq[IR.Op] =
    Seq.empty
}
case class RemoveMode(val perms: IR.Expression) extends CheckMode {
  def prefix = "remove_"
  def withPerms(perms: IR.Expression): CheckMode = RemoveMode(perms)
  def guarded = false

  def visitPerm(
    runtime: CheckRuntime,
    instanceId: IR.Expression,
    fieldIndex: IR.Expression,
    numFields: IR.Expression,
    expression: String
  ): Seq[IR.Op] = {
    val error = new IR.StringLit(s"No permission to access '$expression'")
    val args = List(perms, instanceId, fieldIndex, error)
    val invoke = new IR.Invoke(runtime.remove, args, None)
    Seq(invoke)
  }

  def visitBool(runtime: CheckRuntime, value: IR.Expression): Seq[IR.Op] =
    Seq.empty
}

class CheckImplementation(
    program: IR.Program,
    val runtime: CheckRuntime,
    structIds: Map[String, IR.StructField]
) {
  private val predicateImplementations =
    mutable.Map[(String, String), Option[IR.MethodDefinition]]()

  private def resolvePredicateDefinition(
      modes: List[CheckMode],
      pred: IR.Predicate
  ): Option[IR.MethodDefinition] = {
    val prefix = modes.map(_.prefix).mkString

    predicateImplementations.getOrElse(
      (prefix, pred.name),
      implementPredicate(modes, pred)
    )
  }

  private def implementPredicate(
      modes: List[CheckMode],
      pred: IR.Predicate
  ): Option[IR.MethodDefinition] = {
    // TODO: allow name collisions when adding methods
    val prefix = modes.map(_.prefix.mkString).mkString
    val methodName = prefix + pred.name

    val defn = program.addMethod(methodName, None)
    predicateImplementations += ((prefix, pred.name) -> Some(defn))

    val predParams = pred.parameters
      .map((p: IR.Var) => p -> defn.addParameter(p.varType, p.name))
      .toMap

    val childModes = modes.map(mode => {
      val paramName = mode.prefix + "perms"
      val param = defn.addParameter(runtime.ownedFieldsRef, paramName)
      mode.withPerms(param)
    })

    val context = new PredicateContext(pred, predParams)
    val ops =
      translate(pred.expression, context, childModes)

    if (ops.nonEmpty) {
      defn.body ++= ops
      Some(defn)
    } else {
      // Otherwise, this predicate implementation is a no-op, and it can be ignored
      // TODO: Remove the no-op method definition
      predicateImplementations.update((prefix, pred.name), None)
      None
    }
  }

  def structIdField(struct: IR.StructDefinition): IR.StructField =
    structIds(struct.name)

  def translate(
    expr: IR.Expression,
    context: SpecificationContext,
    modes: List[CheckMode]
  ): Seq[IR.Op] = expr match {
    case acc: IR.Accessibility =>
      acc.member match {
        case member: IR.FieldMember =>
          translateFieldPermission(member, modes, context)
        case member =>
          throw new WeaverException(
            "Invalid member '" + IRPrinter.print(member) + "' in specification.")
      }
    case instance: IR.PredicateInstance =>
      translatePredicateInstance(instance, modes, context)

    case imp: IR.Imprecise =>
      imp.precise match {
        case None => Seq.empty
        case Some(precise) =>
          translate(precise, context, modes)
      }

    case conditional: IR.Conditional =>
      val trueOps = translate(conditional.ifTrue, context, modes)
      val falseOps = translate(conditional.ifFalse, context, modes)
      val condition = context.convert(conditional.condition)
      (trueOps.isEmpty, falseOps.isEmpty) match {
        case (false, false) =>
          val ifStmt = new IR.If(condition)
          ifStmt.ifTrue ++= trueOps
          ifStmt.ifFalse ++= falseOps
          Seq(ifStmt)

        case (false, true) =>
          val ifStmt = new IR.If(condition)
          ifStmt.ifTrue ++= trueOps
          Seq(ifStmt)

        case (true, false) =>
          val ifStmt =
            new IR.If(new IR.Unary(IR.UnaryOp.Not, condition))
          ifStmt.ifTrue ++= falseOps
          Seq(ifStmt)

        case (true, true) =>
          Seq.empty
      }

    case binary: IR.Binary if binary.operator == IR.BinaryOp.And =>
      Seq.concat(
        translate(binary.left, context, modes),
        translate(binary.right, context, modes)
      )

    case expr => {
      val converted = context.convert(expr)
      modes.flatMap(_.visitBool(runtime, converted))
    }
  }

  def translateFieldPermission(
    member: IR.FieldMember,
    modes: List[CheckMode],
    context: SpecificationContext
  ): Seq[IR.Op] = {
    val converted = context.convert(member)
    val root = converted.root
    val struct = converted.field.struct match {
      case s: IR.Struct =>
        s
      case s =>
        throw new WeaverException("Cannot access fields of struct " + s.name)
    }

    // Get the expression to access the instance ID
    val guarded = modes.exists(_.guarded)
    val instanceId: IR.Expression =
      root.valueType match {
        case None => 
          // If valueType is not defined, there is a NULL dereference in
          // the expression, so we cannot compile it
          if (guarded)
            new IR.IntLit(-1)
          else
            throw new WeaverException("Invalid NULL dereference")
        case Some(_) => {
          val id = new IR.FieldMember(root, structIdField(struct))
          if (guarded) {
            // Convert to `root == null ? -1 : root->_id`
            val nullCheck = new IR.Binary(IR.BinaryOp.Equal, root, new IR.NullLit())
            new IR.Conditional(nullCheck, new IR.IntLit(-1), id)
          } else {
            id
          }
        }
      }
    
    val fieldName = converted.field.name
    val fieldType = converted.field.valueType
    // TODO: Can we just use regular `indexOf`?
    val fieldIndex = new IR.IntLit(struct.fields.indexWhere(
      f => f.name == fieldName && f.valueType == fieldType))
    val numFields = new IR.IntLit(struct.fields.length - 1)
    val expression = IRPrinter.print(converted)
    
    modes.flatMap(_.visitPerm(runtime, instanceId, fieldIndex, numFields, expression))
  }

  def translatePredicateInstance(
    instance: IR.PredicateInstance,
    modes: List[CheckMode],
    context: SpecificationContext
  ): Seq[IR.Op] = {
    // Pass the predicate arguments followed by the permission sets
    val arguments =
      instance.arguments.map(context.convert) ::: modes.map(_.perms)

    resolvePredicateDefinition(modes, instance.predicate)
      .map(new IR.Invoke(_, arguments, None))
      .toSeq
  }

  def trackAllocation(alloc: IR.AllocStruct, perms: IR.Expression): Seq[IR.Op] = {
    val struct = alloc.struct match {
      case s: IR.Struct => s
      case _: IR.DependencyStruct =>
        throw new WeaverException("Cannot allocate library struct")
    }
    val idField = new IR.FieldMember(
      alloc.target,
      structIdField(struct)
    )

    new IR.Invoke(
      runtime.addStruct,
      List(perms, idField, new IR.IntLit(struct.fields.length-1)),
      None
    ) :: Nil
  }

  def permsType: IR.Type = runtime.ownedFieldsRef

  def init(target: IR.Expression): Seq[IR.Op] =
    Seq(new IR.Invoke(runtime.init, Nil, Some(target)))

  def join(target: IR.Expression, source: IR.Expression): Seq[IR.Op] = {
    Seq(new IR.Invoke(runtime.join, List(target, source), None))
  }
}
