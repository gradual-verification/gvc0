package gvc.transformer

// A pass that removes multiple return statements by transforming
//
//     if (cond) return x;
//     else return y;
//
// into
//
//     RETURN_TYPE result;
//     if (cond) result = x;
//     else result = y;
//     return result;
//
// This allows simpler handling of runtime checks for post-conditions.
//
// It also removes redundant `return` statements in the tail position of void
// methods.
//
// NOTE: This **assumes** that there are NO early returns! This assumption is
// checked by gvc.analyzer.ReturnValidator.

object ReturnSimplification {
  def transform(method: IR.Method): Unit = {
    method.returnType match {
      case None => removeReturns(method.body)
      case Some(t) => method.body.lastOption match {
        case Some(_: IR.Return) =>
          // Non-void method ending in a return statement is fine already
          ()
        case _ => {
          // Otherwise, add a new variable, change returns to assignments, and
          // add the single return statement to the method
          val result = method.addVar(t, "result")
          returnToAssignment(method.body, result)
          method.body += new IR.Return(Some(result));
        }
      }
    }
  }

  private def removeReturns(block: IR.Block): Unit = {
    block.lastOption match {
      case Some(ret: IR.Return) => ret.remove()
      case Some(cond: IR.If) => {
        removeReturns(cond.ifFalse)
        removeReturns(cond.ifTrue)
      }
      case _ => ()
    }
  }

  private def returnToAssignment(block: IR.Block, result: IR.Var): Unit =
    block.lastOption match {
      case Some(ret: IR.Return) if ret.value.isDefined => {
        ret.remove()
        block += new IR.Assign(result, ret.value.get)
      }
      case Some(cond: IR.If) => {
        returnToAssignment(cond.ifTrue, result)
        returnToAssignment(cond.ifFalse, result)
      }
      case _ =>
        throw new TransformerException("Could not find return statement in non-void method")
    }
}