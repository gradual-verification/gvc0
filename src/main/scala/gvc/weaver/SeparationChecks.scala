package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR

object SeparationChecks {
  def canOverlap(spec: IR.Expression): Boolean = countAccs(spec) > 1

  // Count the number of acc'd heap locations. Optimized so that if at least 2
  // are found, it may stop counting.
  private def countAccs(spec: IR.Expression): Int = spec match {
    case _: IR.Accessibility => 1

    case b: IR.Binary => {
      val left = countAccs(b.left)
      if (left > 1) left else left + countAccs(b.right)
    }

    case c: IR.Conditional => {
      val left = countAccs(c.ifTrue)
      if (left > 1) left else Math.max(left, countAccs(c.ifFalse))
    }

    case i: IR.Imprecise => i.precise match {
      case None => 0
      case Some(precise) => countAccs(precise)
    }
    
    // Could optimize so that it explores predicats (would have to implement
    // handling for mutually-recursive predicates).
    case p: IR.PredicateInstance => 2

    case _ => 0
  }

  def inject(locations: mutable.HashSet[Location], method: IR.Method, checks: mutable.ListBuffer[RuntimeCheck]): Unit = {
    locations.foreach(loc => {
      val (spec, context) = loc match {
        case at: AtOp => at.op match {
          case call: IR.Invoke => {
            call.callee match {
              case m: IR.Method if m.precondition.isDefined =>
                (m.precondition.get, new CallSiteContext(call))
              case _ =>
                throw new WeaverException("Invalid method definition")
            }
          }

          case f: IR.Fold => {
            val p = f.instance.predicate
            val params: Seq[IR.Var] = p.parameters
            val args = params.zip(f.instance.arguments).toMap
            (p.expression, new PredicateContext(p, args))
          }

          case w: IR.While =>
            (w.invariant, ValueContext)

          case a: IR.Assert =>
            (a.value, ValueContext)

          case op =>
            throw new WeaverException(s"Cannot check separation at $op")
        }

        case MethodPost if method.postcondition.isDefined => {
          (method.postcondition.get, IdentityContext)
        }
      }

      if (canOverlap(spec))
        inject(spec, loc, None, context, checks)
    })
  }

  private def inject(
    spec: IR.Expression,
    loc: Location,
    cond: Option[CheckExpression],
    context: SpecificationContext,
    checks: mutable.ListBuffer[RuntimeCheck]
  ): Unit = {
    spec match {
      case acc: IR.Accessibility =>
        CheckExpression.irValue(context.convertExpression(acc.member)) match {
          case f: CheckExpression.Field => {
            checks += RuntimeCheck(
              loc,
              FieldSeparationCheck(f),
              cond.map(ImmediateCondition)
            )
          }
          case _ => throw new WeaverException("Invalid acc value")
        }

      case b: IR.Binary if b.operator == IR.BinaryOp.And => {
        inject(b.left, loc, cond, context, checks)
        inject(b.right, loc, cond, context, checks)
      }

      case c: IR.Conditional => {
        val t = CheckExpression.irValue(context.convertExpression(c.condition))
        val f = CheckExpression.Not(t)
        val (trueCond, falseCond) = cond match {
          case None =>
            (t, f)
          case Some(cond) =>
            (CheckExpression.And(cond, t), CheckExpression.And(cond, f))
        }

        inject(c.ifTrue, loc, Some(trueCond), context, checks)
        inject(c.ifFalse, loc, Some(falseCond), context, checks)
      }

      case i: IR.Imprecise =>
        i.precise match {
          case None => ()
          case Some(spec) => inject(spec, loc, cond, context, checks)
        }

      case p: IR.PredicateInstance => {
        checks += RuntimeCheck(
          loc,
          PredicateSeparationCheck(
            p.predicate.name,
            p.arguments.map(arg =>
              CheckExpression.irValue(context.convertExpression(arg)))
          ),
          cond.map(ImmediateCondition)
        )
      }

      case _ => ()
    }
  }
}
