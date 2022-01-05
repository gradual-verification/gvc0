package gvc.transformer
import IRGraph._

object Replacer {
  type Mapping = Map[Var, Var]

  def replace(block: Block, m: Mapping): Unit =
    block.foreach(replace(_, m))
  
  def replace(op: Op, m: Mapping): Unit = {
    replaceShallow(op, m)

    op match {
      case iff: If => {
        replace(iff.ifTrue, m)
        replace(iff.ifFalse, m)
      }
      case loop: While => {
        replace(loop.body, m)
      }
      case _ => ()
    }
  }

  def replaceShallow(op: Op, m: Mapping): Unit = op match {
    case inv: Invoke => {
      inv.arguments = inv.arguments.map(replace(_, m))
      inv.target = inv.target.map(replace(_, m))
    }
    case alloc: AllocValue => {
      alloc.target = replace(alloc.target, m)
    }
    case alloc: AllocStruct => {
      alloc.target = replace(alloc.target, m)
    }
    case alloc: AllocArray => {
      //TODO: alloc.length
      alloc.target = replace(alloc.target, m)
    }
    case assign: Assign => {
      assign.target = replace(assign.target, m)
      assign.value = replace(assign.value, m)
    }
    case assign: AssignMember => {
      assign.value = replace(assign.value, m)
      assign.member = replace(assign.member, m)
    }
    case assert: Assert => {
      assert.value = replace(assert.value, m)
    }
    case fold: Fold => {
      fold.instance = replace(fold.instance, m)
    }
    case unfold: Unfold => {
      unfold.instance = replace(unfold.instance, m)
    }
    case error: Error => {
      error.value = replace(error.value, m)
    }
    case ret: Return => {
      ret.value = ret.value.map(replace(_, m))
    }
    case iff: If => {
      iff.condition = replace(iff.condition, m)
    }
    case loop: While => {
      loop.condition = replace(loop.condition, m)
    }
  }

  def replace(v: Var, m: Mapping): Var = m.getOrElse(v, v)

  def replace(member: Member, m: Mapping): Member = member match {
    case field: FieldMember => new FieldMember(replace(field.root, m), field.field)
    case deref: DereferenceMember => new DereferenceMember(replace(deref.root, m), deref.valueType)
    case array: ArrayMember => new ArrayMember(replace(array.root, m), array.valueType, array.index) // TODO: index
  }

  def replace(pred: PredicateInstance, m: Mapping): PredicateInstance =
    new PredicateInstance(pred.predicate, pred.arguments.map(replace(_, m)))

  def replace(expr: Expression, m: Mapping): Expression = expr match {
    case v: Var => replace(v, m)
    case member: Member => replace(member, m)
    case acc: Accessibility => new Accessibility(replace(acc.member, m))
    case pred: PredicateInstance => replace(pred, m)
    case result: Result => result
    case imprecise: Imprecise => new Imprecise(imprecise.precise.map(replace(_, m)))
    case literal: Literal => literal
    case cond: Conditional => new Conditional(replace(cond.condition, m), replace(cond.ifTrue, m), replace(cond.ifFalse, m))
    case binary: Binary => new Binary(binary.operator, replace(binary.left, m), replace(binary.right, m))
    case unary: Unary => new Unary(unary.operator, replace(unary.operand, m))
  }
}