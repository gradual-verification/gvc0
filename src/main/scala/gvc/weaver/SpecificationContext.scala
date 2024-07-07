package gvc.weaver
import gvc.transformer.IR
import gvc.transformer.IR

abstract class SpecificationContext {
  def convertVar(source: IR.Var): IR.Expression
  def convertResult(source: IR.Result): IR.Expression

  def convertFieldMember(member: IR.FieldMember): IR.FieldMember = {
    new IR.FieldMember(
      convertExpression(member.root),
      member.field
    )
  }

  def convertExpression(expr: IR.Expression): IR.Expression = {
    expr match {
      case value: IR.Var => convertVar(value)

      case fieldMember: IR.FieldMember =>
        convertFieldMember(fieldMember)

      case derefMember: IR.DereferenceMember =>
        new IR.DereferenceMember(convertExpression(derefMember.root))

      case result: IR.Result => convertResult(result)

      case literal: IR.Literal => literal

      case binary: IR.Binary =>
        new IR.Binary(
          binary.operator,
          convertExpression(binary.left),
          convertExpression(binary.right)
        )

      case unary: IR.Unary =>
        new IR.Unary(unary.operator, convertExpression(unary.operand))

      case cond: IR.Conditional =>
        new IR.Conditional(convertExpression(cond.condition),
                           convertExpression(cond.ifTrue),
                           convertExpression(cond.ifFalse))

      case _: IR.Accessibility | _: IR.Imprecise | _: IR.ArrayMember |
          _: IR.PredicateInstance =>
        throw new WeaverException(
          "Invalid expression; cannot convert to new context."
        )
    }
  }
}

// A context implementation that only validates that invalid expressions
// like \result are not used incorrectly
object ValueContext extends SpecificationContext {
  def convertResult(source: IR.Result): IR.Expression =
    throw new WeaverException("Invalid result expression")

  def convertVar(source: IR.Var): IR.Expression = source
}

object IdentityContext extends SpecificationContext {
  def convertResult(source: IR.Result): IR.Expression = source
  def convertVar(source: IR.Var): IR.Expression = source
  override def convertExpression(expr: IR.Expression): IR.Expression = expr
  override def convertFieldMember(member: IR.FieldMember): IR.FieldMember = member
}

class PredicateContext(pred: IR.Predicate, params: Map[IR.Var, IR.Expression])
    extends SpecificationContext {
  def convertResult(source: IR.Result): IR.Expression =
    throw new WeaverException(s"Invalid \result expression in '${pred.name}'")

  def convertVar(source: IR.Var): IR.Expression =
    params.getOrElse(
      source,
      throw new WeaverException(
        s"Could not find variable '${source.name}' in '${pred.name}'")
    )
}

class ReturnContext(returnValue: IR.Expression) extends SpecificationContext {
  def convertVar(source: IR.Var): IR.Expression =
    source

  def convertResult(source: IR.Result): IR.Expression =
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

  def convertVar(source: IR.Var): IR.Expression =
    variableMapping.getOrElse(
      source,
      throw new WeaverException(
        s"Could not find variable '${source.name} at call site of '${call.callee.name}'"
      ))

  def convertResult(source: IR.Result): IR.Expression = call.target.getOrElse(
    throw new WeaverException("Invoke of non-void method must have a target"))
}
