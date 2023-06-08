package gvteal.analyzer

object ExpressionVisitor {
  type Visitor = (ResolvedExpression) => Unit

  def visit(expr: ResolvedExpression, visitor: Visitor): Unit = {
    visitor(expr)
    expr match {
      case invoke: ResolvedInvoke => invoke.arguments.foreach(visit(_, visitor))
      case member: ResolvedMember => visit(member.parent, visitor)
      case index: ResolvedArrayIndex => {
        visit(index.array, visitor)
        visit(index.index, visitor)
      }
      case ar: ResolvedArithmetic => {
        visit(ar.left, visitor)
        visit(ar.right, visitor)
      }
      case comp: ResolvedComparison => {
        visit(comp.left, visitor)
        visit(comp.right, visitor)
      }
      case ternary: ResolvedTernary => {
        visit(ternary.condition, visitor)
        visit(ternary.ifTrue, visitor)
        visit(ternary.ifFalse, visitor)
      }
      case logical: ResolvedLogical => {
        visit(logical.left, visitor)
        visit(logical.right, visitor)
      }
      case deref: ResolvedDereference => visit(deref.value, visitor)
      case not: ResolvedNot => visit(not.value, visitor)
      case negate: ResolvedNegation => visit(negate.value, visitor)
      case alloc: ResolvedAllocArray => visit(alloc.length, visitor)
      case length: ResolvedLength => visit(length.array, visitor)
      case acc: ResolvedAccessibility => visit(acc.field, visitor)
      case pred: ResolvedPredicate => pred.arguments.foreach(visit(_, visitor))
      case _: ResolvedVariableRef | _: ResolvedAlloc | _: ResolvedResult | _: ResolvedImprecision
        | _: ResolvedInt | _: ResolvedString | _: ResolvedChar | _: ResolvedBool | _: ResolvedNull => ()
    }
  }

  def collectVariables(expr: ResolvedExpression): Set[String] = {
    var vars = Set[String]()
    visit(expr, {
      case ref: ResolvedVariableRef => ref.variable.foreach(vars += _.name)
      case _ => ()
    })

    vars
  }
}