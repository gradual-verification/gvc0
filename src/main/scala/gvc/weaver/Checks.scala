package gvc.weaver
import viper.silver.{ast => vpr}
import gvc.transformer.{IRGraph => ir}
import gvc.transformer.IRGraphSilver.Names
import gvc.transformer.IRGraph

sealed trait Check

object Check {
  def fromViper(
      check: vpr.Exp,
      program: ir.Program,
      method: ir.Method
  ): Check = {
    check match {
      case fieldAccess: vpr.FieldAccessPredicate => {
        val field: CheckExpression.Field = CheckExpression
          .fromViper(fieldAccess.loc, method)
          .asInstanceOf[CheckExpression.Field]
        AccessibilityCheck(field, false, true)
      }
      case predicate: vpr.PredicateAccess => {
        PredicateCheck(
          program.predicate(predicate.predicateName),
          predicate.args
            .map(
              CheckExpression.fromViper(_, method).toIR(program, method, None)
            )
            .toList
        )
      }
      case predicateAccess: vpr.PredicateAccessPredicate => {
        PredicateCheck(
          program.predicate(predicateAccess.loc.predicateName),
          predicateAccess.loc.args
            .map(
              CheckExpression.fromViper(_, method).toIR(program, method, None)
            )
            .toList
        )
      }
      case _ => CheckExpression.fromViper(check, method)

    }
  }
}
case class AccessibilityCheck(
    field: CheckExpression.Field,
    checkSeparate: Boolean,
    checkExists: Boolean
) extends Check

case class PredicateCheck(
    predicate: ir.Predicate,
    args: List[ir.Expression]
) extends Check

sealed trait CheckExpression extends Check {
  def toIR(
      p: ir.Program,
      m: ir.Method,
      returnValue: Option[ir.Expression]
  ): ir.Expression
}

object CheckExpression {
  type Expr = CheckExpression

  sealed trait Binary extends Expr {
    val left: CheckExpression
    val right: CheckExpression
    def op: ir.BinaryOp
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]): ir.Binary =
      new ir.Binary(op, left.toIR(p, m, r), right.toIR(p, m, r))
  }

  case class And(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.And
  }
  case class Or(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Or
  }
  case class Add(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Add
  }
  case class Sub(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Subtract
  }
  case class Mul(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Multiply
  }
  case class Div(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Divide
  }
  case class Eq(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Equal
  }
  case class Lt(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Less
  }
  case class LtEq(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.LessOrEqual
  }
  case class Gt(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.Greater
  }
  case class GtEq(left: Expr, right: Expr) extends Binary {
    def op = ir.BinaryOp.GreaterOrEqual
  }

  sealed trait Unary extends CheckExpression {
    val operand: Expr
    def op: ir.UnaryOp
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]): ir.Unary =
      new ir.Unary(op, operand.toIR(p, m, r))
  }
  case class Not(operand: Expr) extends Unary {
    def op = ir.UnaryOp.Not
  }
  case class Neg(operand: Expr) extends Unary {
    def op = ir.UnaryOp.Negate
  }

  case class Var(name: String) extends Expr {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      m.variable(name)
  }

  case class Field(root: Expr, structName: String, fieldName: String)
      extends Expr {
    def getIRField(p: ir.Program) =
      p.struct(structName)
        .fields
        .find(_.name == fieldName)
        .getOrElse(
          throw new WeaverException(s"Field '$fieldName' does not exist")
        )

    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.FieldMember(root.toIR(p, m, r), getIRField(p))
  }

  case class Deref(operand: Expr) extends Expr {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.DereferenceMember(operand.toIR(p, m, r))
  }

  sealed trait Literal extends Expr
  case class IntLit(value: Int) extends Literal {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.Int(value)
  }
  case class CharLit(value: Char) extends Literal {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.Char(value)
  }
  case class StrLit(value: String) extends Literal {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.String(value)
  }
  case object NullLit extends Literal {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.Null()
  }
  sealed trait BoolLit extends Expr {
    def value: Boolean
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.Bool(value)
  }
  object BoolLit {
    def apply(value: Boolean): BoolLit = if (value) TrueLit else FalseLit
  }
  case object TrueLit extends BoolLit {
    def value = true
  }
  case object FalseLit extends BoolLit {
    def value = false
  }

  case class Cond(cond: Expr, ifTrue: Expr, ifFalse: Expr) extends Expr {
    def toIR(p: ir.Program, m: ir.Method, r: Option[ir.Expression]) =
      new ir.Conditional(
        cond.toIR(p, m, r),
        ifTrue.toIR(p, m, r),
        ifFalse.toIR(p, m, r)
      )
  }

  case object Result extends Expr {
    def toIR(
        p: IRGraph.Program,
        m: IRGraph.Method,
        returnValue: Option[IRGraph.Expression]
    ): IRGraph.Expression =
      returnValue.getOrElse(
        throw new WeaverException("Invalid \result expression")
      )
  }

  def fromViper(value: vpr.Exp, method: ir.Method): Expr = {
    def expr(e: vpr.Exp) = fromViper(e, method)
    value match {
      case eq: vpr.EqCmp  => Eq(expr(eq.left), expr(eq.right))
      case ne: vpr.NeCmp  => Not(Eq(expr(ne.left), expr(ne.right)))
      case lt: vpr.LtCmp  => Lt(expr(lt.left), expr(lt.right))
      case lte: vpr.LeCmp => LtEq(expr(lte.left), expr(lte.right))
      case gt: vpr.GtCmp  => Gt(expr(gt.left), expr(gt.right))
      case gte: vpr.GeCmp => GtEq(expr(gte.left), expr(gte.right))

      case and: vpr.And => And(expr(and.left), expr(and.right))
      case or: vpr.Or   => Or(expr(or.left), expr(or.right))

      case add: vpr.Add => Add(expr(add.left), expr(add.right))
      case sub: vpr.Sub => Sub(expr(sub.left), expr(sub.right))
      case mul: vpr.Mul => Mul(expr(mul.left), expr(mul.right))
      case div: vpr.Div => Div(expr(div.left), expr(div.right))

      case minus: vpr.Minus => Neg(expr(minus.exp))
      case not: vpr.Not =>
        expr(not.exp) match {
          case Not(f) => f
          case x      => Not(x)
        }

      case access: vpr.FieldAccess => {
        val root = expr(access.rcv)
        access.field.name match {
          case Names.BoolPointerValue | Names.IntPointerValue |
              Names.RefPointerValue =>
            Deref(root)
          case field => {
            val segments = field.split('$')
            if (segments.length != 2)
              throw new WeaverException(s"Invalid field name '$field'")
            Field(root, segments(0), segments(1))
          }
        }
      }

      case v: vpr.LocalVar =>
        v.name match {
          case "$return" => Result
          case id        => Var(id)
        }

      case lit: vpr.BoolLit => if (lit.value) TrueLit else FalseLit
      case lit: vpr.IntLit =>
        IntLit(
          lit.i.toInt
        ) // TODO: This could be used as a char type in some circumstances
      case _: vpr.NullLit => NullLit

      case e =>
        throw new WeaverException(
          "Cannot convert Silver expression `" + e.toString() + "`"
        )
    }
  }
}
