package gvc.transformer

object Replacer {
  type Mapping = Map[IR.Var, IR.Var]

  def replace(block: IR.Block, m: Mapping): Unit =
    block.foreach(replace(_, m))

  def replace(op: IR.Op, m: Mapping): Unit = {
    replaceShallow(op, m)

    op match {
      case iff: IR.If => {
        replace(iff.ifTrue, m)
        replace(iff.ifFalse, m)
      }
      case loop: IR.While => {
        replace(loop.body, m)
      }
      case _ => ()
    }
  }

  def replaceShallow(op: IR.Op, m: Mapping): Unit = op match {
    case inv: IR.Invoke => {
      inv.arguments = inv.arguments.map(replace(_, m))
      inv.target = inv.target.map(replace(_, m))
    }
    case alloc: IR.AllocValue => {
      alloc.target = replace(alloc.target, m)
    }
    case alloc: IR.AllocStruct => {
      alloc.target = replace(alloc.target, m)
    }
    case alloc: IR.AllocArray => {
      //TODO: alloc.length
      alloc.target = replace(alloc.target, m)
    }
    case assign: IR.Assign => {
      assign.target = replace(assign.target, m)
      assign.value = replace(assign.value, m)
    }
    case assign: IR.AssignMember => {
      assign.value = replace(assign.value, m)
      assign.member = replace(assign.member, m)
    }
    case assert: IR.Assert => {
      assert.value = replace(assert.value, m)
    }
    case fold: IR.Fold => {
      fold.instance = replace(fold.instance, m)
    }
    case unfold: IR.Unfold => {
      unfold.instance = replace(unfold.instance, m)
    }
    case error: IR.Error => {
      error.value = replace(error.value, m)
    }
    case ret: IR.Return => {
      ret.value = ret.value.map(replace(_, m))
    }
    case iff: IR.If => {
      iff.condition = replace(iff.condition, m)
    }
    case loop: IR.While => {
      loop.condition = replace(loop.condition, m)
      loop.invariant = replace(loop.invariant, m)
    }
  }

  // Recursively follows all mappings
  // Note that this could cause an infinite loop if a cycle of mappings occurred
  // (i.e. v1 -> v2 -> v1)
  def replace(v: IR.Var, m: Mapping): IR.Var = m.get(v) match {
    case None            => v
    case Some(mappedVar) => replace(mappedVar, m)
  }

  def replace(member: IR.Member, m: Mapping): IR.Member = member match {
    case field: IR.FieldMember =>
      new IR.FieldMember(replace(field.root, m), field.field, field.resolved)
    case deref: IR.DereferenceMember =>
      new IR.DereferenceMember(replace(deref.root, m), deref.resolved)
    case array: IR.ArrayMember =>
      new IR.ArrayMember(replace(array.root, m), array.index, array.resolved) // TODO: index
  }

  def replace(pred: IR.PredicateInstance, m: Mapping): IR.PredicateInstance =
    new IR.PredicateInstance(pred.predicate, pred.arguments.map(replace(_, m)), pred.resolved)

  def replace(expr: IR.Expression, m: Mapping): IR.Expression = expr match {
    case v: IR.Var                  => replace(v, m)
    case member: IR.Member          => replace(member, m)
    case acc: IR.Accessibility      => new IR.Accessibility(replace(acc.member, m), acc.resolved)
    case pred: IR.PredicateInstance => replace(pred, m)
    case result: IR.Result          => result
    case imprecise: IR.Imprecise =>
      new IR.Imprecise(imprecise.precise.map(replace(_, m)), imprecise.resolved)
    case literal: IR.Literal => literal
    case cond: IR.Conditional =>
      new IR.Conditional(replace(cond.condition, m),
                         replace(cond.ifTrue, m),
                         replace(cond.ifFalse, m),
                         cond.resolved)
    case binary: IR.Binary =>
      new IR.Binary(binary.operator,
                    replace(binary.left, m),
                    replace(binary.right, m),
                    binary.resolved)
    case unary: IR.Unary =>
      new IR.Unary(unary.operator, replace(unary.operand, m), unary.resolved)
  }
}
