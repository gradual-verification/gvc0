package gvc.transformer
import scala.collection.mutable
import gvc.transformer.IR.Var

// Transforms the method 
object AssignmentTransformer {
  class AssignmentRewriter extends IRRewriter {
    val variables = mutable.Map[IR.Var, IR.Var]()
    val allocated = mutable.ListBuffer[IR.Var]()
    var assigned = List[(IR.Var, IR.Var)]()

    def rewriteArgs(args: List[IR.Var]): List[IR.Var] = {
      // Remove all argument variables from the map
      // An argument may be unused, in which case the variable will not be in
      // the map. If it is unused, just use the original variable to represent
      // the argument.
      args.map(arg => variables.remove(arg).getOrElse(arg))
    }

    override def block(block: IR.Block): IR.Block = {
      // Iterate in reverse order
      var ops: List[IR.Op] = Nil
      for (op <- block.operations.reverseIterator) {
        ops = Rewriter.rewriteOp(this, op) :: ops
      }

      new IR.Block(ops)
    }

    // Map a variable to its corresponding variable in the map, or, if it is
    // not in the map, create a new variable and add its mapping to the old
    // variable.
    override def variable(variable: Var): Var = {
      variables.get(variable) match {
        case Some(value) => value
        case None => {
          val newVar = ??? //new IR.Var(variable.varType, variable.nameHint) TODO: Implement var naming
          variables += (variable -> newVar)
          allocated += newVar
          newVar
        }
      }
    }

    override def operation(op: IR.Op): IR.Op = {
      op match {
        case assign: IR.Op.AssignVar => {
          // Remove the variable before rewriting the RHS, so any use in the RHS
          // will access a new variable copy
          val removed = variables.remove(assign.subject)
          val value = Rewriter.rewriteExpr(this, assign.value)

          // If the variable is not in the map of variables, it is not used
          // after this assignment, so the assignment can be converted to a noop.
          removed match {
            case None => new IR.Op.Noop(assign.value)
            case Some(newVar) => {
              assigned = (newVar -> assign.subject) :: assigned
              new IR.Op.AssignVar(newVar, value)
            }
          }
        }

        case iff: IR.Op.If => {
          val oldAssigned = assigned
          
          assigned = Nil
          val ifTrue = block(iff.ifTrue)
          val assignedIfTrue = assigned

          assigned = Nil
          val ifFalse = block(iff.ifFalse)
          val assignedIfFalse = assigned

          assigned = assignedIfTrue ::: assignedIfFalse ::: oldAssigned

          val additionalTrueAssignments = assignedIfFalse.map { case (newVar, oldVar) => new IR.Op.AssignVar(newVar, variable(oldVar)) }
          val additionalFalseAssignments = assignedIfTrue.map { case (newVar, oldVar) => new IR.Op.AssignVar(newVar, variable(oldVar)) }

          new IR.Op.If(value(iff.condition), new IR.Block(additionalTrueAssignments ::: ifTrue.operations), new IR.Block(additionalFalseAssignments ::: ifFalse.operations))
        }

        case loop: IR.Op.While => {
          val oldAssigned = assigned

          assigned = Nil
          val body = block(loop.body)
          val assignedInLoop = assigned

          assigned = assignedInLoop ::: oldAssigned

          ???
        }

        case _ => Rewriter.rewriteOp(this, op)
      }
    }
  }

  def transform(method: IR.MethodImplementation): IR.MethodImplementation = {
    val rewriter = new AssignmentRewriter()
    val body = rewriter.block(method.body)
    val args = rewriter.rewriteArgs(method.arguments)

    // Arguments that are used are added to the allocated list, so remove them
    // before determining the list of declared variables in the method.
    val variables = rewriter.allocated.filter(v => args.contains(v)).toList

    // Use-before-assign errors should be detected before this pass
    if (!rewriter.variables.isEmpty) throw new TransformerException("Use of unassigned variable detected")

    new IR.MethodImplementation(method.name, method.returnType, args, variables, body)
  }
}