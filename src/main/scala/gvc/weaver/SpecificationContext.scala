package gvc.weaver
import gvc.transformer.IR
import gvc.transformer.IR
import gvc.transformer.IR.PredicateInstance

abstract class SpecificationContext {
  def convert(v: IR.Var): IR.Expression
  def convert(r: IR.Result): IR.Expression

  def convert(f: IR.FieldMember): IR.FieldMember =
    new IR.FieldMember(convert(f.root), f.field)
  def convert(d: IR.DereferenceMember): IR.DereferenceMember =
    new IR.DereferenceMember(convert(d.root))
  def convert(l: IR.Literal): IR.Literal =
    l
  def convert(b: IR.Binary): IR.Binary =
    new IR.Binary(b.operator, convert(b.left), convert(b.right))
  def convert(u: IR.Unary): IR.Unary =
    new IR.Unary(u.operator, u.operand)
  def convert(c: IR.Conditional): IR.Conditional =
    new IR.Conditional(convert(c.condition), convert(c.ifTrue), convert(c.ifFalse))
  def convert(a: IR.Accessibility): IR.Accessibility =
    throw new WeaverException("Cannot translate acc(...) to new context")
  def convert(p: IR.PredicateInstance): IR.PredicateInstance =
    throw new WeaverException("Cannot translate " + p.predicate.name + "(...) to new context")
  def convert(a: IR.ArrayMember): IR.ArrayMember =
    throw new WeaverException("Cannot translate array access to new context")
  def convert(u: IR.Unfolding): IR.Expression = 
    convert(u.expr)

  def convert(expr: IR.Expression): IR.Expression = {
    expr match {
      case v: IR.Var => convert(v)
      case f: IR.FieldMember => convert(f)
      case d: IR.DereferenceMember => convert(d)
      case r: IR.Result => convert(r)
      case l: IR.Literal => convert(l)
      case b: IR.Binary => convert(b)
      case u: IR.Unary => convert(u)
      case c: IR.Conditional => convert(c)
      case a: IR.Accessibility => convert(a)
      case i: IR.Imprecise => convert(i)
      case p: PredicateInstance => convert(p)
      case a: IR.ArrayMember => convert(a)
      case u: IR.Unfolding => convert(u)
    }
  }
}

// A context implementation that only validates that invalid expressions
// like \result are not used incorrectly
object ValueContext extends SpecificationContext {
  def convert(source: IR.Result): IR.Expression =
    throw new WeaverException("Invalid result expression")

  def convert(source: IR.Var): IR.Expression = source
}

object IdentityContext extends SpecificationContext {
  def convert(source: IR.Result): IR.Expression = source
  def convert(source: IR.Var): IR.Expression = source
  override def convert(expr: IR.Expression): IR.Expression = expr
  override def convert(f: IR.FieldMember): IR.FieldMember = f
  override def convert(p: IR.PredicateInstance): IR.PredicateInstance = p
  override def convert(a: IR.Accessibility): IR.Accessibility = a
  override def convert(a: IR.ArrayMember): IR.ArrayMember = a
}

class PredicateContext(pred: IR.Predicate, params: Map[IR.Var, IR.Expression])
    extends SpecificationContext {
  def convert(source: IR.Result): IR.Expression =
    throw new WeaverException(s"Invalid \result expression in '${pred.name}'")

  def convert(source: IR.Var): IR.Expression =
    params.getOrElse(
      source,
      throw new WeaverException(
        s"Could not find variable '${source.name}' in '${pred.name}'")
    )
}

class ReturnContext(returnValue: IR.Expression) extends SpecificationContext {
  def convert(source: IR.Var): IR.Expression =
    source

  def convert(source: IR.Result): IR.Expression =
    returnValue
}

// A context implementation that maps parameters to their actual values using
// the arguments specified at a given call site
// If 'NULL' is passed as a parameter, it is replaced with a temporary variable to avoid
// generating runtime checks or permission tracking operations with dereferences of the form 'NULL->'
class CallSiteContext(call: IR.Invoke)
    extends SpecificationContext {
  val variableMapping: Map[IR.Var, IR.Expression] =
    (call.callee.parameters zip call.arguments)
      .map(_ match {
        case (param, _: IR.NullLit) => {
            val validValueType = param.valueType match {
              case Some(value) => value
              case None =>
                throw new WeaverException(
                  s"Couldn't resolve parameter value type for parameter ${param.name} of method ${call.callee.name}")
            }
            (param, call.method.addVar(validValueType))
        }
        case pair => pair
      })
      .toMap

  def convert(source: IR.Var): IR.Expression =
    variableMapping.getOrElse(
      source,
      throw new WeaverException(
        s"Could not find variable '${source.name} at call site of '${call.callee.name}'"
      ))

  def convert(source: IR.Result): IR.Expression = call.target.getOrElse(
    throw new WeaverException("Invoke of non-void method must have a target"))
}
