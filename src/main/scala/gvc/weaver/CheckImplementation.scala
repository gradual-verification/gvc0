package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR

sealed trait CheckMode {
  def prefix: String
}

case object CheckAddRemoveMode extends CheckMode {
  def prefix = "check_add_remove_"
}

case object CheckAddMode extends CheckMode {
  def prefix = "check_add_"
}

case object AddMode extends CheckMode {
  def prefix = "add_"
}

case object AddRemoveMode extends CheckMode {
  def prefix = "add_remove_"
}

case object RemoveMode extends CheckMode {
  def prefix = "remove_"
}

case object SeparationMode extends CheckMode {
  def prefix = "sep_"
}

case object VerifyMode extends CheckMode {
  def prefix = ""
}

sealed trait CheckType

case object Separation extends CheckType

case object Verification extends CheckType

class CheckImplementation(
                           program: IR.Program,
                           val runtime: CheckRuntime,
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

    val permsPrimary = defn.addParameter(
      runtime.ownedFieldsRef,
      CheckRuntime.Names.primaryOwnedFields
    )

    val permsSecondary =
      if (mode == AddRemoveMode || mode == CheckAddMode || mode == CheckAddRemoveMode)
        Some(
          defn.addParameter(
            runtime.ownedFieldsRef,
            CheckRuntime.Names.temporaryOwnedFields
          ))
      else None

    val context = new PredicateContext(pred, newParams)
    val ops =
      translate(mode, pred.expression, permsPrimary, permsSecondary, context)

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

  def structIdField(struct: IR.StructDefinition): IR.StructField =
    structIds(struct.name)

  def translate(
                 mode: CheckMode,
                 expr: IR.Expression,
                 permsPrimary: IR.Var,
                 permsSecondary: Option[IR.Var],
                 context: SpecificationContext,
               ): Seq[IR.Op] = expr match {
    case acc: IR.Accessibility =>
      acc.member match {
        case member: IR.FieldMember =>
          translateFieldPermission(mode,
            member,
            permsPrimary,
            permsSecondary,
            context)
        case _ =>
          throw new WeaverException("Invalid conjunct in specification.")
      }
    case pred: IR.PredicateInstance =>
      translatePredicateInstance(mode,
        pred,
        permsPrimary,
        permsSecondary,
        context)

    case imp: IR.Imprecise =>
      imp.precise match {
        case None => Seq.empty
        case Some(precise) =>
          translate(mode, precise, permsPrimary, permsSecondary, context)
      }

    case conditional: IR.Conditional =>
      val trueOps = translate(mode,
        conditional.ifTrue,
        permsPrimary,
        permsSecondary,
        context)
      val falseOps = translate(mode,
        conditional.ifFalse,
        permsPrimary,
        permsSecondary,
        context)
      val condition = context.convertExpression(conditional.condition)
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
      translate(mode, binary.left, permsPrimary, permsSecondary, context) ++ translate(
        mode,
        binary.right,
        permsPrimary,
        permsSecondary,
        context
      )


    case expr =>
      mode match {
        case SeparationMode | AddMode | RemoveMode | AddRemoveMode =>
          Seq.empty
        case VerifyMode | CheckAddMode | CheckAddRemoveMode =>
          val toAssert = context.convertExpression(expr)
          Seq(new IR.Assert(toAssert, IR.AssertKind.Imperative))
        
      }
  }

  def translateFieldPermission(
                                mode: CheckMode,
                                member: IR.FieldMember,
                                permsPrimary: IR.Var,
                                permsSecondary: Option[IR.Var],
                                context: SpecificationContext
                              ): Seq[IR.Op] = {
    println("not converted member:")
    member.field.struct.fields.foreach{ f => print(f.name + " ")}
    println("")
    val convertedMember = context.convertFieldMember(member)
    val struct = convertedMember.field.struct
    println(struct.fields.length)
    print("Fields: ")
    struct.fields.foreach{f => print(f.name + " ")}
    println("");
    val idFieldExists = struct.fields.exists(fld => {
      fld.name == "_id"
    })
    if (!idFieldExists) {
      throw new WeaverException("Couldn't locate _id field")
    }
    val instanceId =
      if (convertedMember.root.valueType.isDefined) {
        mode match {
          case SeparationMode | VerifyMode | CheckAddRemoveMode |
               CheckAddMode =>
            new IR.Conditional(
              new IR.Binary(
                IR.BinaryOp.NotEqual,
                convertedMember.root,
                new IR.NullLit()
              ),
              new IR.FieldMember(convertedMember.root, structIdField(struct)),
              new IR.IntLit(-1)
            )
          case AddMode | RemoveMode | AddRemoveMode =>
            // If it's in add/remove, it doesn't need the null check
            new IR.FieldMember(convertedMember.root, structIdField(struct))
        }
      } else {
        // If valueType is not defined, there is a NULL dereference in
        // the expression, so we cannot compile it
        mode match {
          case SeparationMode | VerifyMode =>
            new IR.IntLit(-1)
          case AddMode | RemoveMode | AddRemoveMode | CheckAddRemoveMode |
               CheckAddMode =>
            throw new WeaverException("Invalid NULL dereference")
        }
      }

    val fieldIndex = new IR.IntLit(struct.fields.indexOf(convertedMember.field))
    val numFields = new IR.IntLit(struct.fields.length)
    //TODO: add support for IRPrinter.printExpr here
    val fullName = s"struct ${struct.name}.${convertedMember.field.name}"

    mode match {
      case SeparationMode =>
        val error =
          new IR.StringLit(s"Overlapping field permissions for $fullName")
        Seq(
          new IR.Invoke(
            runtime.addAccEnsureSeparate,
            List(permsPrimary, instanceId, fieldIndex, numFields, error),
            None
          )
        )
      case VerifyMode =>
        val error =
          new IR.StringLit(s"Field access runtime check failed for $fullName")
        Seq(
          new IR.Invoke(
            runtime.assertAcc,
            List(permsPrimary, instanceId, fieldIndex, error),
            None
          )
        )
      case RemoveMode =>
        Seq(
          new IR.Invoke(
            runtime.loseAcc,
            List(permsPrimary, instanceId, fieldIndex),
            None
          )
        )

      // TODO: We need to also add permissions required for framing
      case AddMode =>
        Seq(
          new IR.Invoke(
            runtime.addAcc,
            List(permsPrimary, instanceId, numFields, fieldIndex),
            None
          )
        )
      case CheckAddRemoveMode =>
        val error =
          new IR.StringLit(s"Field access runtime check failed for $fullName")
        permsSecondary match {
          case Some(secondary) =>
            Seq(
              new IR.Invoke(
                runtime.assertAcc,
                List(secondary, instanceId, fieldIndex, error),
                None
              ),
              new IR.Invoke(
                runtime.addAcc,
                List(permsPrimary, instanceId, numFields, fieldIndex),
                None
              ),
              new IR.Invoke(
                runtime.loseAcc,
                List(secondary, instanceId, fieldIndex),
                None
              )
            )
          case None =>
            throw new WeaverException(
              "Missing temporary OwnedFields struct reference for CheckAddRemove mode.")
        }
      case CheckAddMode =>
        val error =
          new IR.StringLit(s"Field access runtime check failed for $fullName")
        permsSecondary match {
          case Some(secondary) =>
            Seq(
              new IR.Invoke(
                runtime.assertAcc,
                List(secondary, instanceId, fieldIndex, error),
                None
              ),
              new IR.Invoke(
                runtime.addAcc,
                List(permsPrimary, instanceId, numFields, fieldIndex),
                None
              )
            )
          case None =>
            throw new WeaverException(
              "Missing temporary OwnedFields struct reference for CheckAdd mode.")
        }
      case AddRemoveMode =>
        permsSecondary match {
          case Some(secondary) =>
            Seq(
              new IR.Invoke(
                runtime.addAcc,
                List(permsPrimary, instanceId, numFields, fieldIndex),
                None
              ),
              new IR.Invoke(
                runtime.loseAcc,
                List(secondary, instanceId, fieldIndex),
                None
              )
            )
          case None =>
            throw new WeaverException(
              "Missing temporary OwnedFields struct reference for AddRemove mode.")
        }

    }
  }

  def translatePredicateInstance(
                                  mode: CheckMode,
                                  pred: IR.PredicateInstance,
                                  permsPrimary: IR.Var,
                                  permsSecondary: Option[IR.Var],
                                  context: SpecificationContext
                                ): Seq[IR.Op] = {
    val arguments = pred.arguments.map(context.convertExpression)

    val toAppend = mode match {

      case AddRemoveMode | CheckAddRemoveMode | CheckAddMode =>
        permsSecondary match {
          case Some(value) => List(permsPrimary, value)
          case None =>
            throw new WeaverException(
              "Missing secondary OwnedFields reference for optimized permission tracking mode.")
        }
      case _ => List(permsPrimary)
    }
    resolvePredicateDefinition(mode, pred.predicate)
      .map(new IR.Invoke(_, arguments ++ toAppend, None))
      .toSeq
  }

  def trackAllocation(alloc: IR.AllocStruct, perms: IR.Var): Unit = {
    val structType = alloc.struct
    val idField = new IR.FieldMember(
      alloc.target,
      structIdField(alloc.struct)
    )

    alloc.insertAfter(
      new IR.Invoke(
        runtime.addStructAcc,
        List(perms, new IR.IntLit(structType.fields.length)),
        Some(idField)
      )
    )
  }

  def idAllocation(alloc: IR.AllocStruct,
                   instanceCounter: IR.Expression): Unit = {
    val idField = new IR.FieldMember(
      alloc.target,
      structIdField(alloc.struct)
    )

    alloc.insertAfter(
      Seq(
        new IR.AssignMember(idField, new IR.DereferenceMember(instanceCounter)),
        new IR.AssignMember(
          new IR.DereferenceMember(instanceCounter),
          new IR.Binary(IR.BinaryOp.Add,
            new IR.DereferenceMember(instanceCounter),
            new IR.IntLit(1)))
      ))
  }
}
