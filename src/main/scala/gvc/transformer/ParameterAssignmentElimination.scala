package gvc.transformer

import IRGraph._
import scala.collection.mutable

// Removes all assignments to parameters. If a parameter is assigned a value,
// a new variable is added. All instances of the parameter are replaced with
// the new variable. Then, at the beginning of the method, the new variable is
// aliased to the parameter. This pass is necessary because Silver does not
// allow assignments to parameters.
object ParameterAssignmentElimination {
  def transform(method: Method): Unit = {
    val reassigned = mutable.Set[Parameter]()
    traverse(method.body, reassigned)

    if (reassigned.nonEmpty) {
      val replacements = reassigned.toSeq
        .sortBy(method.parameters.indexOf(_))
        .asInstanceOf[Seq[Var]]
        .map(p => p -> method.addVar(p.varType, p.name))
      Replacer.replace(method.body, replacements.toMap)
      for ((p, v) <- replacements) {
        new IRGraph.Assign(v, p) +=: method.body
      }
    }
  }

  def traverse(block: Block, collect: mutable.Set[Parameter]): Unit = {
    block.foreach(traverse(_, collect))
  }

  def traverse(op: Op, collect: mutable.Set[Parameter]): Unit = op match {
    case assign: Assign => assign.target match {
      case param: Parameter => collect += param
      case _ => ()
    }
    case alloc: AllocArray => alloc.target match {
      case param: Parameter => collect += param
      case _ => ()
    }
    case alloc: AllocStruct => alloc.target match {
      case param: Parameter => collect += param
      case _ => ()
    }
    case alloc: AllocValue => alloc.target match {
      case param: Parameter => collect += param
      case _ => ()
    }
    case invoke: Invoke => invoke.target match {
      case Some(param: Parameter) => collect += param
      case _ => ()
    }
    case iff: If => {
      traverse(iff.ifTrue, collect)
      traverse(iff.ifFalse, collect)
    }
    case loop: While => {
      traverse(loop.body, collect)
    }
    case _ => ()
  }
}