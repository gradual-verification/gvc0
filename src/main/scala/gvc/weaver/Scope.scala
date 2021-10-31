package gvc.weaver

import gvc.transformer.IR
import scala.collection.mutable

class Scope(method: IR.MethodImplementation) {
  private var counter = 0;
  private val arguments = Map(method.arguments.map(v => v.name -> v): _*)
  private val vars = mutable.Map(method.variables.map(v => v.name -> v): _*)

  def define(t: IR.Type) = {
    // TODO: Implement collision handling
    counter += 1
    val newVar = new IR.Var(t, s"__$counter")
    vars += newVar.name -> newVar
    newVar
  }

  def lookupVar(name: String) = vars.get(name) match {
    case None => arguments.get(name) match {
      case None => throw new Weaver.WeaverException("Could not find variable " + name)
      case Some(arg) => arg
    }
    case Some(v) => v
  }

  def getVars() = vars.values.toSeq.sortWith(_.name < _.name).toList
}