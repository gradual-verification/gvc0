package gvc.weaver

import gvc.transformer.IR
import viper.silver.{ast => vpr}

object CheckImplementation {

  def generate(check: vpr.Exp, scope: Scope, returnValue: Option[IR.Value]): Seq[IR.Op] = {
    val (ops, exp) = expression(check, scope, returnValue)
    val assert = new IR.Op.Assert(exp)

    ops :+ assert
  }

  def expression(exp: vpr.Exp, scope: Scope, returnValue: Option[IR.Value]): (Seq[IR.Op], IR.Value) = {
    exp match {
      case eq: vpr.EqCmp => {
        val (leftOps, left) = expression(eq.left, scope, returnValue)
        val (rightOps, right) = expression(eq.right, scope, returnValue)

        val compVar = scope.define(IR.Type.Bool)
        val compOp = new IR.Op.AssignVar(compVar, new IR.Expr.Comparison(left, right, IR.ComparisonOp.Equal));
        
        (leftOps ++ rightOps :+ compOp, compVar)
      }

      case v: vpr.LocalVar => {
        if (v.name == "$return") {
          returnValue match {
            case Some(ret) => (Seq(), ret)
            case None => throw new Weaver.WeaverException("Invalid access to return value")
          }
        } else {
          val variable = scope.lookupVar(v.name)
          (Seq(), variable)
        }
      }

      case lit: vpr.BoolLit => (Seq(), new IR.Literal.Bool(lit.value))
      case lit: vpr.IntLit => (Seq(), new IR.Literal.Int(lit.i.toInt))

      case _ => ???
    }
  }
}