package gvc.transformer

trait IRRewriter {
  def variable(variable: IR.Var): IR.Var = variable

  def value(value: IR.Value): IR.Value = {
    value match {
      case v: IR.Var => variable(v)
      case v => v
    }
  }

  def expression(expr: IR.Expr): IR.Expr = Rewriter.rewriteExpr(this, expr)

  def operation(op: IR.Op): IR.Op = Rewriter.rewriteOp(this, op)

  def block(block: IR.Block): IR.Block = new IR.Block(block.operations.map(Rewriter.rewriteOp(this, _)))
}

object Rewriter {
  def rewriteValue(rewriter: IRRewriter, value: IR.Value): IR.Value = {
    val newVal = value match {
      case v: IR.Var => rewriter.variable(v)
      case v => v
    }

    rewriter.value(newVal)
  }

  def rewriteExpr(rewriter: IRRewriter, expr: IR.Expr): IR.Expr = {
    val rval = rewriteValue(rewriter, _)
    val rvar = rewriter.variable(_)

    expr match {
      case x: IR.Literal => x
      case x: IR.Var => rvar(x)
      case x: IR.Expr.Arithmetic => new IR.Expr.Arithmetic(rval(x.left), rval(x.right), x.op)
      case x: IR.Expr.Comparison => new IR.Expr.Comparison(rval(x.left), rval(x.right), x.op)
      case x: IR.Expr.Logical => new IR.Expr.Logical(rval(x.left), rval(x.right), x.op)
      case x: IR.Expr.ArrayAccess => new IR.Expr.ArrayAccess(rvar(x.subject), rval(x.index))
      case x: IR.Expr.ArrayFieldAccess => new IR.Expr.ArrayFieldAccess(rvar(x.subject), rval(x.index), x.field)
      case x: IR.Expr.Deref => new IR.Expr.Deref(rvar(x.subject))
      case x: IR.Expr.Negation => new IR.Expr.Negation(rval(x.value))
      case x: IR.Expr.Not => new IR.Expr.Not(rval(x.value))
      case x: IR.Expr.Member => new IR.Expr.Member(rvar(x.subject), x.field)
      case x: IR.Expr.Alloc => x
      case x: IR.Expr.AllocArray => new IR.Expr.AllocArray(x.memberType, rval(x.length))
      case x: IR.Expr.Invoke => new IR.Expr.Invoke(x.methodName, x.arguments.map(rval), x.returnType)
    }
  }

  def rewriteOp(rewriter: IRRewriter, op: IR.Op): IR.Op = {
    val rexpr = rewriter.expression(_)
    val rval = rewriter.value(_)
    val rvar = rewriter.variable(_)
    val rewrittenOp = op match {
      case x: IR.Op.AssignVar => new IR.Op.AssignVar(rvar(x.subject), rexpr(x.value))
      case x: IR.Op.AssignMember => new IR.Op.AssignMember(rvar(x.subject), x.field, rval(x.value))
      case x: IR.Op.AssignArray => new IR.Op.AssignArray(rvar(x.subject), rval(x.index), rval(x.value))
      case x: IR.Op.AssignArrayMember => new IR.Op.AssignArrayMember(rvar(x.subject), rval(x.index), x.field, rval(x.value))
      case x: IR.Op.AssignPtr => new IR.Op.AssignPtr(rvar(x.subject), rval(x.value))
      // TODO: Rewrite invariant
      case x: IR.Op.While => new IR.Op.While(rval(x.condition), x.invariant, rewriter.block(x.body))
      case x: IR.Op.If => new IR.Op.If(rval(x.condition), rewriter.block(x.ifTrue), rewriter.block(x.ifFalse))
      case x: IR.Op.Assert => new IR.Op.Assert(rval(x.value))
      case x: IR.Op.Error => new IR.Op.Error(rval(x.value))
      case x: IR.Op.Return => new IR.Op.Return(x.value.map(rval))
      case x: IR.Op.Noop => new IR.Op.Noop(rexpr(x.value))
    }

    rewriter.operation(rewrittenOp)
  }
}