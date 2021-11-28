package gvc.weaver

import gvc.transformer.IRGraph._
import viper.silver.{ast => vpr}

object CheckImplementation {

  def generate(check: vpr.Exp, method: Method, returnValue: Option[Expression]): Seq[Op] = {
    val exp = expression(check, method, returnValue)
    Seq(new Assert(exp, AssertMethod.Imperative))
  }

  def expression(exp: vpr.Exp, method: Method, returnValue: Option[Expression]): Expression = {
    exp match {
      case eq: vpr.EqCmp => new Binary(
        BinaryOp.Equal,
        expression(eq.left, method, returnValue),
        expression(eq.right, method, returnValue))
        
      case v: vpr.LocalVar => v.name match {
        case "$return" => returnValue.getOrElse(throw new Weaver.WeaverException("Invalid access to return value"))
        case id => method.variable(id)
      }

      case lit: vpr.BoolLit => new Bool(lit.value)

      // TODO: This could be used as a char type in some circumstances
      case lit: vpr.IntLit => new Int(lit.i.toInt)

      case _ => ???
    }
  }
}