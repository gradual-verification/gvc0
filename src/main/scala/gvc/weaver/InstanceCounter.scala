package gvc.weaver

import gvc.transformer.IR

object InstanceCounter {
  private val counterRef = new IR.PointerType(IR.IntType)
  private val counterName = "instanceCounter"

  def inject(program: IR.Program, idFields: Map[String, IR.StructField]): Unit = {
    program.methods.foreach(inject(_, idFields))
  }

  private def inject(
    method: IR.Method,
    idFields: Map[String, IR.StructField]
  ): Unit = {
    val counter = method.name match {
      case "main" => {
        val counter = method.addVar(counterRef, counterName)
        new IR.AllocValue(IR.IntType, counter) +=: method.body
        counter
      }
      case _ => method.addParameter(counterRef, counterName)
    }

    inject(method.body, counter, idFields)
  }

  private def inject(block: IR.Block, counter: IR.Var, idFields: Map[String, IR.StructField]): Unit = {
    block.foreach(_ match {
      case call: IR.Invoke if call.callee.name != "main" =>
        call.arguments :+= counter
      case cond: IR.If => {
        inject(cond.ifTrue, counter, idFields)
        inject(cond.ifFalse, counter, idFields)
      }
      case loop: IR.While => {
        inject(loop.body, counter, idFields)
      }
      case alloc: IR.AllocStruct => {
        idFields.get(alloc.struct.name).foreach(field => {
          val deref = new IR.DereferenceMember(counter)
          val idField = new IR.FieldMember(alloc.target, field)
          alloc.insertAfter(List(
            new IR.AssignMember(idField, deref),
            new IR.AssignMember(deref, new IR.Binary(IR.BinaryOp.Add, deref, new IR.IntLit(1)))
          ))
        })
      }
      case _ => ()
    })
  }
}