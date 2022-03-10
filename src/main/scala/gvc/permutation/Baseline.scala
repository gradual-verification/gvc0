package gvc.permutation

import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{
  AllocStruct,
  AllocValue,
  Block,
  Expression,
  FieldMember,
  Int,
  IntType,
  Invoke,
  Method,
  Op,
  PointerType,
  Predicate,
  PredicateInstance,
  Program,
  StructField,
  Var
}
import gvc.weaver.{
  CheckImplementation,
  CheckRuntime,
  FieldAccessibilityCheck,
  FieldPermissionCheck,
  FieldSeparationCheck,
  PredicateAccessibilityCheck,
  PredicatePermissionCheck,
  PredicateSeparationCheck,
  SeparationMode,
  VerifyMode,
  WeaverException
}

import scala.collection.mutable

val CollectedChecks

object Baseline {

  def insert(program: Program): Unit = {
    val runtime = CheckRuntime.addToIR(program);

    // Add the _id field to each struct
    // Keep a separate map since the name may be something other than `_id` due
    // to name collision avoidance
    val structIdFields = program.structs
      .map(s => (s.name, s.addField(CheckRuntime.Names.id, IntType)))
      .toMap

    val implementation =
      new CheckImplementation(program, runtime, structIdFields)

    program.methods.foreach(insert(program, _, runtime, implementation))
  }

  private def insert(
      program: Program,
      method: Method,
      runtime: CheckRuntime,
      implementation: CheckImplementation
  ): Unit = {

    val initializeOps = mutable.ListBuffer[Op]()
    val allocations = mutable.ListBuffer[Op]()

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


  }
}
