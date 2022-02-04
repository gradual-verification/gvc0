package gvc.weaver

import scala.io.Source
import fastparse.Parsed.{Failure, Success}
import gvc.parser.Parser
import gvc.analyzer.{ErrorSink, ResolvedProgram, Resolver}
import gvc.transformer.IRGraph._
import gvc.transformer.{DependencyTransformer, IRGraph}

import scala.collection.mutable

object CheckRuntime {
  val name = "runtime"

  private lazy val header: ResolvedProgram = {
    val runtimeSource = Source.fromResource("runtime.h0").mkString
    val parsed = Parser.parseProgram(runtimeSource) match {
      case _: Failure =>
        throw new WeaverException("Cannot parse runtime header")
      case Success(value, _) => value
    }

    val errors = new ErrorSink()
    val resolved = Resolver.resolveProgram(parsed, errors)
    if (errors.errors.nonEmpty)
      throw new WeaverException("Cannot resolve runtime header")

    resolved
  }

  def addToIR(program: IRGraph.Program): CheckRuntime = {
    val dependency = program.addDependency(name, isLibrary = true)
    DependencyTransformer.transform(program, dependency, header)
    new CheckRuntime(program)
  }

  object Names {
    val ownedFieldsStruct = "OwnedFields"
    val fieldArray = "FieldArray"
    val primaryOwnedFields = "_ownedFields"
    val temporaryOwnedFields = "_tempFields"
    val initOwnedFields = "initOwnedFields"
    val addStructAcc = "addStructAcc"
    val addAcc = "addAcc"
    val loseAcc = "loseAcc"
    val addDisjointAcc = "addDisjointAcc"
    val join = "join"
    val disjoin = "disjoin"
    val assertAcc = "assertAcc"
    val assertDisjointAcc = "assertDisjointAcc"
    val find = "find"
    val instanceCounter = "_instanceCounter"
    val id = "_id"
    val removePrefix = "remove_"
    val addPrefix = "add_"
  }
}

class CheckRuntime private (program: IRGraph.Program) {
  import CheckRuntime.Names
  val ownedFields: IRGraph.StructDefinition =
    program.struct(Names.ownedFieldsStruct)
  val ownedFieldsRef = new IRGraph.ReferenceType(ownedFields)
  val ownedFieldInstanceCounter: StructField =
    ownedFields.fields.find(_.name == "instanceCounter").get

  val initOwnedFields: IRGraph.MethodDefinition =
    program.method(Names.initOwnedFields)
  val addStructAcc: IRGraph.MethodDefinition =
    program.method(Names.addStructAcc)
  val addAcc: IRGraph.MethodDefinition = program.method(Names.addAcc)
  val loseAcc: IRGraph.MethodDefinition = program.method(Names.loseAcc)
  val addDisjointAcc: IRGraph.MethodDefinition =
    program.method(Names.addDisjointAcc)
  val join: IRGraph.MethodDefinition = program.method(Names.join)
  val disjoin: IRGraph.MethodDefinition = program.method(Names.disjoin)
  val assertAcc: IRGraph.MethodDefinition = program.method(Names.assertAcc)
  val assertDisjointAcc: IRGraph.MethodDefinition =
    program.method(Names.assertDisjointAcc)
  val find: IRGraph.MethodDefinition = program.method(Names.find)

  val removalPredicates
      : mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition] =
    mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition]()
  val additionPredicates
      : mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition] =
    mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition]()

  def resolveAdditionPredicate(
      pred: Predicate,
      structIdFields: Map[scala.Predef.String, StructField]
  ): MethodDefinition = {
    resolvePredicate(
      pred,
      additionPredicates,
      Names.addPrefix,
      addFieldAccess,
      structIdFields
    )
  }

  def resolveRemovalPredicate(
      pred: Predicate,
      structIdFields: Map[scala.Predef.String, StructField]
  ): MethodDefinition = {
    resolvePredicate(
      pred,
      removalPredicates,
      Names.removePrefix,
      removeFieldAccess,
      structIdFields
    )
  }

  def resolvePredicate(
      pred: Predicate,
      predMap: mutable.Map[Predicate, MethodDefinition],
      prefix: scala.Predef.String,
      fieldAccessMutator: (
          FieldMember,
          Var,
          Map[scala.Predef.String, StructField]
      ) => Invoke,
      structFields: Map[scala.Predef.String, StructField]
  ): MethodDefinition = {
    if (predMap.contains(pred)) {
      predMap(pred)
    } else {
      val predicateMethod =
        program.addMethod(prefix + pred.name, None)
      val ownedFieldsInstanceParameter = predicateMethod.addParameter(
        new ReferenceType(ownedFields),
        Names.primaryOwnedFields
      )
      translateSpec(
        pred.expression,
        fieldAccessMutator,
        ownedFieldsInstanceParameter,
        structFields
      ).foreach(op => predicateMethod.body += op)
      predMap += (pred -> predicateMethod)
      predicateMethod
    }
  }

  def assignIDFromInstanceCounter(
      alloc: AllocStruct,
      instanceCounter: Var
  ): Unit = {
    /* increment *(_instance_counter) */

    val deref_inst_counter = new DereferenceMember(instanceCounter)
    alloc.insertAfter(
      new AssignMember(
        deref_inst_counter,
        new Binary(
          BinaryOp.Add,
          deref_inst_counter,
          new IRGraph.Int(1)
        )
      )
    )
    /* assign the new instance's _id field to the current value of *(_instance_counter) */
    alloc.insertAfter(
      new AssignMember(
        new FieldMember(
          alloc.target,
          new StructField(
            alloc.struct.asInstanceOf[Struct],
            CheckRuntime.Names.id,
            IntType
          )
        ),
        new DereferenceMember(instanceCounter)
      )
    )
  }

  def addFieldAccess(
      member: FieldMember,
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Invoke = {
    val struct = member.field.struct
    val instanceId =
      new FieldMember(member.root, structIdFields(struct.name))
    val fieldIndex = new Int(struct.fields.indexOf(member.field))
    val numFields = new Int(struct.fields.length)
    new Invoke(
      addAcc,
      List(
        ownedFieldsTarget,
        instanceId,
        numFields,
        fieldIndex
      ),
      None
    )
  }

  def removeFieldAccess(
      member: FieldMember,
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Invoke = {
    val struct = member.field.struct
    val instanceId = new FieldMember(member.root, structIdFields(struct.name))
    val fieldIndex = new Int(struct.fields.indexOf(member.field))
    new Invoke(
      addAcc,
      List(
        ownedFieldsTarget,
        instanceId,
        fieldIndex
      ),
      None
    )
  }

  def removePermissionsFromContract(
      contract: Option[IRGraph.Expression],
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Seq[Op] = {
    contract.toSeq.flatMap(
      translateSpec(_, removeFieldAccess, ownedFieldsTarget, structIdFields)
    )
  }

  def addPermissionsFromContract(
      contract: Option[IRGraph.Expression],
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Seq[Op] = {
    contract.toSeq.flatMap(
      translateSpec(_, addFieldAccess, ownedFieldsTarget, structIdFields)
    )
  }

  def translateSpec(
      expr: IRGraph.Expression,
      permissionHandler: (
          FieldMember,
          Var,
          Map[scala.Predef.String, StructField]
      ) => Invoke,
      ownedFieldsInstance: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Seq[Op] = {
    expr match {
      case accessibility: IRGraph.Accessibility =>
        accessibility.member match {
          case member: FieldMember =>
            Seq(permissionHandler(member, ownedFieldsInstance, structIdFields))
          case _ =>
            throw new WeaverException("Invalid conjunct in specification.")
        }

      case instance: PredicateInstance => ???
      // TODO: Seq(callPredicate(instance, methodData))

      case imprecise: IRGraph.Imprecise =>
        throw new WeaverException("Invalid spec")

      case conditional: IRGraph.Conditional => {
        val trueOps =
          translateSpec(
            conditional.ifTrue,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields
          ).toList
        val falseOps =
          translateSpec(
            conditional.ifFalse,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields
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
          ownedFieldsInstance,
          structIdFields
        ) ++
          translateSpec(
            binary.right,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields
          )

      case expr =>
        Seq(new IRGraph.Assert(expr, IRGraph.AssertKind.Imperative))
    }
  }
}
