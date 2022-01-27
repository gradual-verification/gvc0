package gvc.weaver

import scala.io.Source
import fastparse.Parsed.{Failure, Success}
import gvc.parser.Parser
import gvc.analyzer.{ErrorSink, ResolvedProgram, Resolver}
import gvc.transformer.IRGraph.{
  AllocStruct,
  AssertKind,
  AssignMember,
  Binary,
  BinaryOp,
  DereferenceMember,
  FieldMember,
  If,
  Int,
  IntType,
  Invoke,
  MethodDefinition,
  Op,
  Predicate,
  PredicateInstance,
  ReferenceType,
  Struct,
  StructField,
  Var
}
import gvc.transformer.{DependencyTransformer, IRGraph}
import gvc.weaver.Collector.{
  CollectedMethod,
  ImpreciseCallStyle,
  PrecisePreCallStyle
}
import viper.silicon.state.reconstructedPermissions
import viper.silver.ast.MethodCall

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
    val primaryOwnedFields = "fields"
    val temporaryOwnedFields = "tempFields"
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

  val equirecursivePredicates: mutable.Map[String, MethodDefinition] =
    mutable.Map[String, MethodDefinition]()

  def addDynamicStructAccess(
      alloc: AllocStruct,
      ownedFields: Var
  ): Unit = {
    val structType = alloc.struct
    alloc.insertAfter(
      new Invoke(
        addStructAcc,
        List(ownedFields, new Int(structType.fields.length - 1)),
        Some(
          new FieldMember(
            alloc.target,
            new StructField(structType.asInstanceOf[Struct], Names.id, IntType)
          )
        )
      )
    )
  }

  def resolvePrimaryOwnedFields(methodData: CollectedMethod): Var = {
    if (
      methodData.callStyle == PrecisePreCallStyle || methodData.callStyle == ImpreciseCallStyle
    ) {
      val currentEntry = methodData.method.parameters.find(p =>
        p.name == Names.primaryOwnedFields && p.valueType.isDefined && p.valueType.get
          .isInstanceOf[ReferenceType] && p.valueType.get
          .asInstanceOf[ReferenceType]
          .struct
          .equals(ownedFields)
      )
      currentEntry match {
        case Some(entry) => entry
        case None =>
          methodData.method.addParameter(
            new ReferenceType(ownedFields),
            Names.primaryOwnedFields
          )
      }
    } else {
      val currentEntry = methodData.method.getVar(Names.primaryOwnedFields)
      currentEntry match {
        case Some(value) => value
        case None        => methodData.method.addVar(new ReferenceType(ownedFields))
      }
    }
  }

  def resolveTemporaryOwnedFields(methodData: CollectedMethod): Var = {
    val currentEntry = methodData.method.getVar(Names.temporaryOwnedFields)
    if (
      currentEntry.isDefined && currentEntry.get.valueType.isDefined && currentEntry.get.valueType.get
        .isInstanceOf[ReferenceType] && currentEntry.get.valueType.get
        .asInstanceOf[ReferenceType]
        .struct == ownedFields
    ) {
      currentEntry.get
    } else {
      methodData.method.addVar(
        new ReferenceType(ownedFields),
        Names.temporaryOwnedFields
      )
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

  def callPredicate(
      pred: PredicateInstance,
      methodData: CollectedMethod
  ): Op = {
    new Invoke(
      resolvePredicate(pred.predicate, methodData),
      pred.arguments ++ List(resolveTemporaryOwnedFields(methodData)),
      None
    )
  }

  def resolvePredicate(
      pred: Predicate,
      methodData: CollectedMethod
  ): IRGraph.MethodDefinition =
    equirecursivePredicates.get(pred.name) match {
      case Some(value) => value
      case None =>
        val defn = program.addMethod(pred.name, None)
        equirecursivePredicates += pred.name -> defn
        translateSpec(
          pred.expression,
          resolveTemporaryOwnedFields(methodData),
          addAccess,
          methodData
        ).foreach(op => defn.body += op)
        defn
    }

  def removePermissionsFromContract(
      contract: Option[IRGraph.Expression],
      methodData: CollectedMethod
  ): Seq[Op] = {
    contract match {
      case Some(value) =>
        translateSpec(
          value,
          resolveTemporaryOwnedFields(methodData),
          loseAccess,
          methodData
        )
      case None => Seq()
    }
  }

  def addPermissionsFromContract(
      contract: Option[IRGraph.Expression],
      methodData: CollectedMethod
  ): Seq[Op] = {
    contract match {
      case Some(value) =>
        translateSpec(
          value,
          resolveTemporaryOwnedFields(methodData),
          addAccess,
          methodData
        )
      case None => Seq()
    }
  }

  private def addAccess(target: Var, fm: FieldMember): Invoke = {
    val struct = fm.field.struct
    val fieldIndex = struct.fields.indexOf(fm.field)
    new Invoke(
      addAcc,
      List(
        target,
        new FieldMember(
          fm.root,
          new StructField(
            fm.field.struct,
            CheckRuntime.Names.id,
            IntType
          )
        ),
        new Int(fm.field.struct.fields.length),
        new Int(fieldIndex)
      ),
      None
    )
  }
  private def loseAccess(target: Var, fm: FieldMember): Invoke = {
    val struct = fm.field.struct
    val fieldIndex = struct.fields.indexOf(fm.field)
    new Invoke(
      addAcc,
      List(
        target,
        new FieldMember(
          fm.root,
          new StructField(
            fm.field.struct,
            CheckRuntime.Names.id,
            IntType
          )
        ),
        new Int(fieldIndex)
      ),
      None
    )
  }

  def loadPermissionsBeforeInvocation(
      call: MethodCall,
      methodData: CollectedMethod
  ): Seq[Op] =
    reconstructedPermissions
      .getPermissionsFor(call)
      .flatMap(p => {
        p.permissions
          .map(CheckExpression.fromViper(_, methodData.method))
          .filter(_.isInstanceOf[CheckExpression.Field])
          .map(asExpr => {
            val field = asExpr.asInstanceOf[CheckExpression.Field]
            val structField = field.getIRField(program)
            val struct = structField.struct
            val fieldIndex = struct.fields.indexOf(structField)
            new Invoke(
              addAcc,
              List(
                resolveTemporaryOwnedFields(methodData),
                new FieldMember(
                  field.root.toIR(program, methodData.method, None),
                  structField
                ),
                new Int(fieldIndex)
              ),
              None
            )
          })
      })

  def translateSpec(
      expr: IRGraph.Expression,
      target: Var,
      permissionHandler: (Var, FieldMember) => Invoke,
      methodData: CollectedMethod
  ): Seq[Op] = {
    expr match {
      case expression: IRGraph.SpecificationExpression =>
        expression match {
          case accessibility: IRGraph.Accessibility =>
            val member = accessibility.member
            member match {
              case fm: FieldMember =>
                Seq(permissionHandler(target, fm))
              case _ =>
                throw new WeaverException("Invalid conjunct in specification.")
            }
          case instance: PredicateInstance =>
            Seq(callPredicate(instance, methodData))
          case imprecise: IRGraph.Imprecise =>
            imprecise.precise match {
              case Some(value) =>
                translateSpec(
                  value,
                  target,
                  permissionHandler,
                  methodData
                )
              case None => Seq()
            }
          case _ =>
            throw new WeaverException("Invalid conjunct in specification.")
        }
      case conditional: IRGraph.Conditional =>
        val ifstmt = new If(conditional.condition)
        translateSpec(
          conditional.ifTrue,
          target,
          permissionHandler,
          methodData
        ).foreach(_ => ifstmt.ifTrue += _)
        translateSpec(
          conditional.ifFalse,
          target,
          permissionHandler,
          methodData
        ).foreach(_ => ifstmt.ifFalse += _)
        Seq(ifstmt)
      case binary: Binary =>
        binary.operator match {
          case BinaryOp.And =>
            translateSpec(
              binary.left,
              target,
              permissionHandler,
              methodData
            ) ++ translateSpec(
              binary.right,
              target,
              permissionHandler,
              methodData
            )
          case _ => Seq(new IRGraph.Assert(binary, AssertKind.Imperative))
        }
      case _ => throw new WeaverException("Invalid conjunct in specification.")
    }
  }
}
