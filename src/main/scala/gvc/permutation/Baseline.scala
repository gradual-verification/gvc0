package gvc.permutation

import gvc.transformer.IRGraph.{
  AllocValue,
  FieldMember,
  IntType,
  Invoke,
  Method,
  Op,
  PointerType,
  Program,
  Var
}
import gvc.weaver.{CheckImplementation, CheckRuntime}

import scala.collection.mutable

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
