package gvc.weaver

import gvc.transformer.IRGraph._
import viper.silver.ast.{FieldAccessPredicate}
import viper.silver.{ ast => vpr}

object CheckImplementation {

  def generate(check: viper.silicon.state.CheckInfo, method: Method, returnValue: Option[Expression]): Seq[Op] = {
    check.checks match {
      case FieldAccessPredicate(loc, _) => {
        AccessChecks.visited += method
        AccessChecks.assertFieldAccess(check, loc, method)
      }
      case _ => Seq(new Assert(expression(check.checks, method, returnValue), AssertMethod.Imperative))
    }
  }

  def expression(exp: vpr.Exp, method: Method, returnValue: Option[Expression]): Expression = {
    exp match {
      case eq: vpr.EqCmp => new Binary(
        BinaryOp.Equal,
        expression(eq.left, method, returnValue),
        expression(eq.right, method, returnValue))
        
      case v: vpr.LocalVar => v.name match {
        case "$return" => returnValue.getOrElse(throw new WeaverException("Invalid access to return value"))
        case id => method.variable(id)
      }

      case lit: vpr.BoolLit => new Bool(lit.value)

      // TODO: This could be used as a char type in some circumstances
      case lit: vpr.IntLit => new Int(lit.i.toInt)

      case _ => ???
    }
  }
}