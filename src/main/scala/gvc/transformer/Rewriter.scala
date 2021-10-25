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

  def specification(spec: IR.SpecExpr): IR.SpecExpr = spec
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
      case x: IR.ProgramExpr.Arithmetic => new IR.ProgramExpr.Arithmetic(rval(x.left), rval(x.right), x.op)
      case x: IR.ProgramExpr.Comparison => new IR.ProgramExpr.Comparison(rval(x.left), rval(x.right), x.op)
      case x: IR.ProgramExpr.Logical => new IR.ProgramExpr.Logical(rval(x.left), rval(x.right), x.op)
      case x: IR.ProgramExpr.ArrayAccess => new IR.ProgramExpr.ArrayAccess(rvar(x.subject), rval(x.index))
      case x: IR.ProgramExpr.ArrayFieldAccess => new IR.ProgramExpr.ArrayFieldAccess(rvar(x.subject), rval(x.index), x.field)
      case x: IR.ProgramExpr.Deref => new IR.ProgramExpr.Deref(rvar(x.subject))
      case x: IR.ProgramExpr.Negation => new IR.ProgramExpr.Negation(rval(x.value))
      case x: IR.ProgramExpr.Not => new IR.ProgramExpr.Not(rval(x.value))
      case x: IR.ProgramExpr.Member => new IR.ProgramExpr.Member(rvar(x.subject), x.field)
      case x: IR.ProgramExpr.Alloc => x
      case x: IR.ProgramExpr.AllocArray => new IR.ProgramExpr.AllocArray(x.memberType, rval(x.length))
      case x: IR.ProgramExpr.Invoke => new IR.ProgramExpr.Invoke(x.name, x.arguments.map(rval), x.returnType)
    }
  }

  def rewriteOp(rewriter: IRRewriter, op: IR.Op): IR.Op = {
    val rexpr = rewriter.expression(_)
    val rval = rewriter.value(_)
    val rvar = rewriter.variable(_)
    val rspec = rewriter.specification(_)

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
      case x: IR.Op.AssertSpecExpr => new IR.Op.AssertSpecExpr(rspec(x.spec))
      case x: IR.Op.Error => new IR.Op.Error(rval(x.value))
      case x: IR.Op.Return => new IR.Op.Return(x.value.map(rval))
      case x: IR.Op.Noop => new IR.Op.Noop(rexpr(x.value))
    }

    rewriter.operation(rewrittenOp)
  }
}