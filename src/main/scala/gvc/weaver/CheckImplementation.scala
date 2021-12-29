package gvc.weaver

import gvc.transformer.IRGraph._
import gvc.weaver.AccessChecks.AccessTracker
import viper.silicon.state.CheckInfo
import viper.silver.ast.MethodCall
import viper.silver.{ast => vpr}

object CheckImplementation {

  def generate(
      check: CheckInfo,
      method: Method,
      returnValue: Option[Expression],
      tracker: AccessTracker
  ): Seq[Op] = {
    check.checks match {
      case vpr.FieldAccessPredicate(loc, _) =>
        tracker.visited += method.name
        AccessChecks.assertFieldAccess(check, loc, method, tracker)
      case _ =>
        Seq(
          new Assert(
            expression(check.checks, method, returnValue),
            AssertMethod.Imperative
          )
        )
    }
  }

  def expression(
      exp: vpr.Exp,
      method: Method,
      returnValue: Option[Expression]
  ): Expression = {
    exp match {
      case eq: vpr.EqCmp =>
        new Binary(
          BinaryOp.Equal,
          expression(eq.left, method, returnValue),
          expression(eq.right, method, returnValue)
        )

      case v: vpr.LocalVar =>
        v.name match {
          case "$return" =>
            returnValue.getOrElse(
              throw new WeaverException("Invalid access to return value")
            )
          case id => method.variable(id)
        }

      case lit: vpr.BoolLit => new Bool(lit.value)

      // TODO: This could be used as a char type in some circumstances
      case lit: vpr.IntLit => new Int(lit.i.toInt)

      case _ => ???
    }
  }
}
