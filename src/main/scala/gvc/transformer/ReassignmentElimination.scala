package gvc.transformer

import scala.collection.immutable.ListMap
import gvc.transformer.IRGraph._

// This transformation removes cases of `x = f(x)`, because Silver does not support this pattern.
// The basic idea is to assign to a new variable, and then use that variable anywhere the original
// variable is used in the following code. This is somewhat challenging when dealing with branches
// (if) and loops (while).
object ReassignmentElimination {
  def transform(method: Method): Unit = {
    val transformation = new ReassignmentElimination(method)
    val reassign = new transformation.Reassignments(Map.empty, ListMap.empty, ListMap.empty)

    method.body.foreach(transformation.replace(_, reassign))
  }
}

class ReassignmentElimination(method: Method) {
  class Reassignments(
    var mappings: Map[Var, Var],
    var created: ListMap[Var, Var],
    var remaining: ListMap[Var, Var]) {

    def reassign(v: Var): Var = {
      val newV = remaining.get(v) match {
        case Some(newV) => {
          remaining -= v
          newV
        }
        case None => method.addVar(v.valueType, v.name)
      }

      created += v -> newV
      mappings += v -> newV
      newV
    }

    def assign(v: Var): Var =
      remaining.get(v)
        .map(newV => {
          remaining -= v
          created += v -> newV
          mappings += v -> newV
          newV
        })
        .getOrElse(v)
  }

  def replace(op: Op, reassign: Reassignments): Unit = {
    op match {
      case inv: Invoke => {
        inv.arguments = inv.arguments.map(replace(_, reassign))
        inv.target = inv.target.map(replace(_, reassign))

        inv.target = inv.target.map {
          case v: Var if inv.arguments.exists(_.contains(v)) =>
            reassign.reassign(v)
          case other => other
        }
      }
      case alloc: AllocValue => {
        alloc.target = replace(alloc.target, reassign)
      }
      case alloc: AllocStruct => {
        alloc.target = replace(alloc.target, reassign)
      }
      case alloc: AllocArray => {
        //TODO: alloc.length
        alloc.target = replace(alloc.target, reassign)
      }
      case assign: Assign => {
        assign.target = replace(assign.target, reassign)
        assign.value = replace(assign.value, reassign)

        // Attempt to minimize the number of "patched" assignments by using
        // the variable from the remaining list if one exists
        assign.target = reassign.assign(assign.target)
      }
      case assign: AssignMember => {
        assign.value = replace(assign.value, reassign)
        assign.member = replace(assign.member, reassign)
      }
      case assert: Assert => {
        assert.value = replace(assert.value, reassign)
      }
      case fold: Fold => {
        fold.instance = replace(fold.instance, reassign)
      }
      case unfold: Unfold => {
        unfold.instance = replace(unfold.instance, reassign)
      }
      case error: Error => {
        error.value = replace(error.value, reassign)
      }
      case ret: Return => {
        ret.value = ret.value.map(replace(_, reassign))
      }
      case iff: If => {
        iff.condition = replace(iff.condition, reassign)

        val trueReassign = new Reassignments(reassign.mappings, ListMap(), reassign.remaining)
        iff.ifTrue.foreach(replace(_, trueReassign))

        val falseReassign = new Reassignments(reassign.mappings, ListMap(), reassign.remaining ++ trueReassign.created)
        iff.ifFalse.foreach(replace(_, falseReassign))

        // Any mappings created in the false branch and not in the true branch
        // are "patched up" by aliasing in the true branch
        (falseReassign.created -- trueReassign.created.keys)
          .foreach { case (oldV, newV) => iff.ifTrue += new Assign(newV, oldV) }
        // Same thing, but for the false branch
        (trueReassign.created -- falseReassign.created.keys)
          .foreach { case (oldV, newV) => iff.ifFalse += new Assign(newV, oldV) }

        val created = trueReassign.created ++ falseReassign.created
        reassign.created = reassign.created ++ created
        reassign.remaining = reassign.remaining -- created.keys
        reassign.mappings = reassign.mappings ++ created
      }
      case loop: While => {
        loop.condition = replace(loop.condition, reassign)

        // Any mappings created inside the loop body are "undone" at the end of the loop
        // body, thus code after the loop body (the conditional, following code, or the
        // next loop iteration) is unaffected.

        val bodyReassign = new Reassignments(reassign.mappings, ListMap.empty, ListMap.empty)
        loop.body.foreach(replace(_, bodyReassign))

        bodyReassign.created.foreach {
          case (oldV, newV) => loop.body += new Assign(oldV, newV)
        }
      }
    }
  }

  def replace(v: Var, reassign: Reassignments): Var = reassign.mappings.getOrElse(v, v)

  def replace(member: Member, reassign: Reassignments): Member = member match {
    case field: FieldMember => new FieldMember(replace(field.root, reassign), field.field)
    case deref: DereferenceMember => new DereferenceMember(replace(deref.root, reassign), deref.valueType)
    case array: ArrayMember => new ArrayMember(replace(array.root, reassign), array.valueType, array.index) // TODO: index
  }

  def replace(pred: PredicateInstance, reassign: Reassignments): PredicateInstance =
    new PredicateInstance(pred.predicate, pred.arguments.map(replace(_, reassign)))

  def replace(expr: Expression, reassign: Reassignments): Expression = expr match {
    case v: Var => replace(v, reassign)
    case member: Member => replace(member, reassign)
    case acc: Accessibility => new Accessibility(replace(acc.member, reassign))
    case pred: PredicateInstance => replace(pred, reassign)
    case result: Result => result
    case imprecise: Imprecise => new Imprecise(imprecise.precise.map(replace(_, reassign)))
    case literal: Literal => literal
    case cond: Conditional => new Conditional(replace(cond.condition, reassign), replace(cond.ifTrue, reassign), replace(cond.ifFalse, reassign))
    case binary: Binary => new Binary(binary.operator, replace(binary.left, reassign), replace(binary.right, reassign))
    case unary: Unary => new Unary(unary.operator, replace(unary.operand, reassign))
  }

}