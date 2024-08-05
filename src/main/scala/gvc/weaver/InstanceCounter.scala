package gvc.weaver

import gvc.transformer.IR
import scala.collection.mutable

object InstanceCounter {
  private val counterRef = new IR.PointerType(IR.IntType)
  private val counterName = "_instanceCounter"

  def inject(methods: Seq[IR.Method], idFields: Map[String, IR.StructField]): Unit = {
    val names = mutable.HashSet[String]()
    for (m <- methods) {
      val name = m.name
      if (name != "main")
        names += name
    }

    methods.foreach(inject(_, names, idFields))
  }

  private def inject(
    method: IR.Method,
    methods: mutable.HashSet[String],
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

    inject(method.body, methods, counter, idFields)
  }

  private def inject(
    block: IR.Block,
    methods: mutable.HashSet[String],
    counter: IR.Var,
    idFields: Map[String, IR.StructField]
  ): Unit = {
    block.foreach(_ match {
      case call: IR.Invoke => call.callee match {
        case m: IR.Method if methods.contains(m.name) =>
          call.arguments :+= counter
        case _ => ()
      }
        
      case cond: IR.If => {
        inject(cond.ifTrue, methods, counter, idFields)
        inject(cond.ifFalse, methods, counter, idFields)
      }
      case loop: IR.While => {
        inject(loop.body, methods, counter, idFields)
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