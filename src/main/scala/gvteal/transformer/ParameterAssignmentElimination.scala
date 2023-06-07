package gvc.transformer

import scala.collection.mutable

// Removes all assignments to parameters. If a parameter is assigned a value,
// a new variable is added. All instances of the parameter are replaced with
// the new variable. Then, at the beginning of the method, the new variable is
// aliased to the parameter. This pass is necessary because Silver does not
// allow assignments to parameters.
object ParameterAssignmentElimination {
  def transform(method: IR.Method): Unit = {
    val reassigned = mutable.Set[IR.Parameter]()
    traverse(method.body, reassigned)

    if (reassigned.nonEmpty) {
      val replacements = reassigned.toSeq
        .sortBy(method.parameters.indexOf(_))
        .asInstanceOf[Seq[IR.Var]]
        .map(p => p -> method.addVar(p.varType, p.name))
      Replacer.replace(method.body, replacements.toMap)
      for ((p, v) <- replacements) {
        new IR.Assign(v, p) +=: method.body
      }
    }
  }

  def traverse(block: IR.Block, collect: mutable.Set[IR.Parameter]): Unit = {
    block.foreach(traverse(_, collect))
  }

  def traverse(op: IR.Op, collect: mutable.Set[IR.Parameter]): Unit = op match {
    case assign: IR.Assign => assign.target match {
      case param: IR.Parameter => collect += param
      case _ => ()
    }
    case alloc: IR.AllocArray => alloc.target match {
      case param: IR.Parameter => collect += param
      case _ => ()
    }
    case alloc: IR.AllocStruct => alloc.target match {
      case param: IR.Parameter => collect += param
      case _ => ()
    }
    case alloc: IR.AllocValue => alloc.target match {
      case param: IR.Parameter => collect += param
      case _ => ()
    }
    case invoke: IR.Invoke => invoke.target match {
      case Some(param: IR.Parameter) => collect += param
      case _ => ()
    }
    case iff: IR.If => {
      traverse(iff.ifTrue, collect)
      traverse(iff.ifFalse, collect)
    }
    case loop: IR.While => {
      traverse(loop.body, collect)
    }
    case _ => ()
  }
}