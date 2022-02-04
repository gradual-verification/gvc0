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
    val runtimeSource = Source.fromResource(name + ".h0").mkString
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
    val checkPrefix = "check_"
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
  val checkPredicates
      : mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition] =
    mutable.Map[IRGraph.Predicate, IRGraph.MethodDefinition]()

  def resolveCheckPredicate(
      pred: Predicate,
      structIdFields: Map[scala.Predef.String, StructField]
  ): MethodDefinition = {
    resolvePredicate(
      pred,
      checkPredicates,
      Names.checkPrefix,
      assertFieldAccess,
      structIdFields,
      resolveCheckPredicate
    )
  }

  def resolveAdditionPredicate(
      pred: Predicate,
      structIdFields: Map[scala.Predef.String, StructField]
  ): MethodDefinition = {
    resolvePredicate(
      pred,
      additionPredicates,
      Names.addPrefix,
      addFieldAccess,
      structIdFields,
      resolveAdditionPredicate
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
      structIdFields,
      resolveRemovalPredicate
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
      structFields: Map[scala.Predef.String, StructField],
      predicateResolutionMethod: (
          Predicate,
          Map[scala.Predef.String, StructField]
      ) => MethodDefinition
  ): MethodDefinition = {
    if (predMap.contains(pred)) {
      predMap(pred)
    } else {
      val predicateMethod =
        program.addMethod(prefix + pred.name, None)
      pred.parameters.foreach(param => {
        predicateMethod.addParameter(param.valueType.get, param.name)
      })
      val ownedFieldsInstanceParameter = predicateMethod.addParameter(
        new ReferenceType(ownedFields),
        Names.primaryOwnedFields
      )
      translateSpec(
        pred.expression,
        fieldAccessMutator,
        ownedFieldsInstanceParameter,
        structFields,
        predicateResolutionMethod
      ).foreach(op => predicateMethod.body += op)
      predMap += (pred -> predicateMethod)
      predicateMethod
    }
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

  def assertFieldAccess(
      member: FieldMember,
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Invoke = {
    val struct = member.field.struct
    val instanceId = new FieldMember(member.root, structIdFields(struct.name))
    val fieldIndex = new Int(struct.fields.indexOf(member.field))
    new Invoke(
      assertAcc,
      List(
        ownedFieldsTarget,
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
  ): Seq[Op] = {
    contract.toSeq.flatMap(
      translateSpec(
        _,
        removeFieldAccess,
        ownedFieldsTarget,
        structIdFields,
        resolveRemovalPredicate
      )
    )
  }

  def addPermissionsFromContract(
      contract: Option[IRGraph.Expression],
      ownedFieldsTarget: Var,
      structIdFields: Map[scala.Predef.String, StructField]
  ): Seq[Op] = {
    contract.toSeq.flatMap(
      translateSpec(
        _,
        addFieldAccess,
        ownedFieldsTarget,
        structIdFields,
        resolveAdditionPredicate
      )
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
      structIdFields: Map[scala.Predef.String, StructField],
      predicateResolutionMethod: (
          Predicate,
          Map[scala.Predef.String, StructField]
      ) => MethodDefinition
  ): Seq[Op] = {
    expr match {
      case accessibility: IRGraph.Accessibility =>
        accessibility.member match {
          case member: FieldMember =>
            Seq(permissionHandler(member, ownedFieldsInstance, structIdFields))
          case _ =>
            throw new WeaverException("Invalid conjunct in specification.")
        }

      case instance: PredicateInstance =>
        Seq(
          new Invoke(
            predicateResolutionMethod(instance.predicate, structIdFields),
            List(ownedFieldsInstance),
            None
          )
        )
      case _: IRGraph.Imprecise =>
        throw new WeaverException("Invalid spec")

      case conditional: IRGraph.Conditional => {
        val trueOps =
          translateSpec(
            conditional.ifTrue,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields,
            predicateResolutionMethod
          ).toList
        val falseOps =
          translateSpec(
            conditional.ifFalse,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields,
            predicateResolutionMethod
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
          structIdFields,
          predicateResolutionMethod
        ) ++
          translateSpec(
            binary.right,
            permissionHandler,
            ownedFieldsInstance,
            structIdFields,
            predicateResolutionMethod
          )
      case expr =>
        Seq(new IRGraph.Assert(expr, IRGraph.AssertKind.Imperative))
    }
  }
}
