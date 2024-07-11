package gvc.weaver
import gvc.transformer.IR
import scala.collection.mutable

// Helper class for determining equi-recursive precision
class EquirecursivePrecision(program: IR.Program) {
  private val predicatePrecision = mutable.HashMap[String, Boolean]()

  def isPrecise(pred: IR.Predicate): Boolean = {
    predicatePrecision.get(pred.name) match {
      case Some(v) => v
      case None => {
        predicatePrecision.update(pred.name, true)
        val result = isPrecise(pred.expression)
        predicatePrecision.update(pred.name, result)
        result
      }
    }
  }

  def isPrecise(e: IR.Expression): Boolean = e match {
    case _: IR.Imprecise => false
    case b: IR.Binary if b.operator == IR.BinaryOp.And =>
      isPrecise(b.left) && isPrecise(b.right)
    case c: IR.Conditional => isPrecise(c.ifTrue) && isPrecise(c.ifFalse)
    case p: IR.PredicateInstance => isPrecise(p.predicate)
    case _ => true
  }

  def isPrecise(e: Option[IR.Expression]): Boolean = e match {
    case None => true
    case Some(e) => isPrecise(e)
  }
}