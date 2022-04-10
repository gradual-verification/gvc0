package gvc.weaver
import viper.silver.{ast => vpr}
import gvc.transformer.{IRGraph => IR}

sealed trait Check

trait CheckMethod {
  def method: IR.Method
  def resultVar(name: String): IR.Expression
}

object Check {
  def fromViper(
      check: vpr.Exp,
      program: IR.Program,
      method: IR.Method
  ): Check = {
    check match {
      case fieldAccess: vpr.FieldAccessPredicate =>
        CheckExpression.fromViper(fieldAccess.loc, method) match {
          case field: CheckExpression.Field => FieldAccessibilityCheck(field)
          case _ =>
            throw new WeaverException(
              s"Invalid field accessibility: $fieldAccess"
            )
        }

      case predicate: vpr.PredicateAccess =>
        PredicateAccessibilityCheck(
          predicate.predicateName,
          predicate.args
            .map(CheckExpression.fromViper(_, method))
            .toList
        )

      case predicateAccess: vpr.PredicateAccessPredicate =>
        Check.fromViper(predicateAccess.loc, program, method)

      case _ =>
        CheckExpression.fromViper(check, method)
    }
  }
}

sealed trait PermissionCheck extends Check
sealed trait SeparationCheck
sealed trait AccessibilityCheck

sealed trait FieldPermissionCheck extends PermissionCheck {
  def field: CheckExpression.Field
}

sealed trait PredicatePermissionCheck extends PermissionCheck {
  def predicateName: String
  def arguments: List[CheckExpression]
}

case class FieldSeparationCheck(field: CheckExpression.Field)
    extends FieldPermissionCheck
    with SeparationCheck
case class FieldAccessibilityCheck(field: CheckExpression.Field)
    extends FieldPermissionCheck
    with AccessibilityCheck
case class PredicateSeparationCheck(
    predicateName: String,
    arguments: List[CheckExpression]
) extends PredicatePermissionCheck
    with SeparationCheck
case class PredicateAccessibilityCheck(
    predicateName: String,
    arguments: List[CheckExpression]
) extends PredicatePermissionCheck
    with AccessibilityCheck

sealed trait CheckExpression extends Check {
  def toIR(
      p: IR.Program,
      m: CheckMethod,
      returnValue: Option[IR.Expression]
  ): IR.Expression

  def guard: Option[CheckExpression]

  def guarded: CheckExpression = CheckExpression.and(guard, this)
}

object CheckExpression {
  type Expr = CheckExpression

  private def and(a: Option[CheckExpression], b: CheckExpression): CheckExpression = a match {
    case None => b
    case Some(a) => CheckExpression.And(a, b)
  }

  private def and(a: Option[CheckExpression], b: Option[CheckExpression]): Option[CheckExpression] = b match {
    case None => a
    case Some(b) => Some(and(a, b))
  }

  sealed trait Binary extends Expr {
    val left: CheckExpression
    val right: CheckExpression
    def op: IR.BinaryOp
    def toIR(
        p: IR.Program,
        m: CheckMethod,
        r: Option[IR.Expression]
    ): IR.Binary =
      new IR.Binary(op, left.toIR(p, m, r), right.toIR(p, m, r))

    def guard = and(left.guard, right.guard)
  }

  case class And(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.And
  }
  case class Or(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Or

    // The left guard must always be satisfied
    // The right guard only needs satisfied if the left condition is false
    override def guard = and(left.guard, right.guard.map(g => Or(left, g)))
  }
  case class Add(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Add
  }
  case class Sub(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Subtract
  }
  case class Mul(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Multiply
  }
  case class Div(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Divide
  }
  case class Eq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Equal
  }
  case class Lt(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Less
  }
  case class LtEq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.LessOrEqual
  }
  case class Gt(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.Greater
  }
  case class GtEq(left: Expr, right: Expr) extends Binary {
    def op = IR.BinaryOp.GreaterOrEqual
  }

  sealed trait Unary extends CheckExpression {
    val operand: Expr
    def op: IR.UnaryOp
    def toIR(
        p: IR.Program,
        m: CheckMethod,
        r: Option[IR.Expression]
    ): IR.Unary =
      new IR.Unary(op, operand.toIR(p, m, r))
    def guard = operand.guard
  }
  case class Not(operand: Expr) extends Unary {
    def op = IR.UnaryOp.Not
  }
  case class Neg(operand: Expr) extends Unary {
    def op = IR.UnaryOp.Negate
  }

  case class Var(name: String) extends Expr {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) = {
      m.method.variable(name)
    }
    def guard = None
  }

  case class ResultVar(name: String) extends Expr {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) = {
      m.resultVar(name)
    }
    def guard = None
  }

  case class Field(root: Expr, structName: String, fieldName: String)
      extends Expr {
    def getIRField(p: IR.Program) =
      p.struct(structName)
        .fields
        .find(_.name == fieldName)
        .getOrElse(
          throw new WeaverException(s"Field '$fieldName' does not exist")
        )

    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.FieldMember(root.toIR(p, m, r), getIRField(p))
    
    def guard = Some(and(root.guard, Not(Eq(root, NullLit))))
  }

  case class Deref(operand: Expr) extends Expr {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.DereferenceMember(operand.toIR(p, m, r))
    def guard = Some(and(operand.guard, Not(Eq(operand, NullLit))))
  }

  sealed trait Literal extends Expr {
    def guard = None
  }

  case class IntLit(value: Int) extends Literal {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.Int(value)
  }
  case class CharLit(value: Char) extends Literal {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.Char(value)
  }
  case class StrLit(value: String) extends Literal {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.String(value)
  }
  case object NullLit extends Literal {
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.Null()
  }
  sealed trait BoolLit extends Literal {
    def value: Boolean
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.Bool(value)
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
    def toIR(p: IR.Program, m: CheckMethod, r: Option[IR.Expression]) =
      new IR.Conditional(
        cond.toIR(p, m, r),
        ifTrue.toIR(p, m, r),
        ifFalse.toIR(p, m, r)
      )
    
    def guard = and(cond.guard, (ifTrue.guard, ifFalse.guard) match {
      case (None, None) => None

      // Have a guard for both paths
      // Use a ternary to switch on the actual condition
      case (Some(tg), Some(fg)) => Some(Cond(cond, tg, fg))

      // Only have a guard for the true path
      // Either the false path is taken, or the true guard must be satisfied
      case (Some(tg), None) => Some(Or(Not(cond), tg))

      // Only have a guard for the false path
      // Either the true path is taken, or the false guard is satisifed
      case (None, Some(fg)) => Some(Or(cond, fg))
    })
  }

  case object Result extends Expr {
    def toIR(
        p: IR.Program,
        m: CheckMethod,
        returnValue: Option[IR.Expression]
    ): IR.Expression =
      returnValue.getOrElse(
        throw new WeaverException("Invalid \\result expression")
      )
    def guard = None
  }

  def irValue(value: IR.Expression): Expr = {
    value match {
      case _: IR.ArrayMember | _: IR.Accessibility | _: IR.PredicateInstance |
          _: IR.Imprecise =>
        throw new WeaverException("Invalid expression used as value in spec")
      case n: IR.Var => Var(n.name)
      case n: IR.FieldMember =>
        Field(irValue(n.root), n.field.struct.name, n.field.name)
      case n: IR.DereferenceMember => Deref(irValue(n.root))
      case n: IR.Result            => Result
      case n: IR.Int               => IntLit(n.value)
      case n: IR.Char              => CharLit(n.value)
      case n: IR.Bool              => BoolLit(n.value)
      case n: IR.String            => StrLit(n.value)
      case n: IR.Null              => NullLit
      case n: IR.Conditional =>
        Cond(irValue(n.condition), irValue(n.ifTrue), irValue(n.ifFalse))
      case n: IR.Binary =>
        val l = irValue(n.left)
        val r = irValue(n.right)
        n.operator match {
          case IR.BinaryOp.Add            => Add(l, r)
          case IR.BinaryOp.Subtract       => Sub(l, r)
          case IR.BinaryOp.Divide         => Div(l, r)
          case IR.BinaryOp.Multiply       => Mul(l, r)
          case IR.BinaryOp.And            => And(l, r)
          case IR.BinaryOp.Or             => Or(l, r)
          case IR.BinaryOp.Equal          => Eq(l, r)
          case IR.BinaryOp.NotEqual       => Not(Eq(l, r))
          case IR.BinaryOp.Less           => Lt(l, r)
          case IR.BinaryOp.LessOrEqual    => LtEq(l, r)
          case IR.BinaryOp.Greater        => Gt(l, r)
          case IR.BinaryOp.GreaterOrEqual => GtEq(l, r)
        }
      case n: IR.Unary =>
        val x = irValue(n.operand)
        n.operator match {
          case IR.UnaryOp.Negate => Neg(x)
          case IR.UnaryOp.Not    => Not(x)
        }
    }
  }

  def fromViper(
      value: vpr.Exp,
      method: IR.Method
  ): Expr = {
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
          case field => {
            val segments = field.split('.')
            var modifiedRoot = root
            val base =
              if (segments.length != 0) segments(segments.length - 1) else field
            val structName = base.split('$')(0)
            val fieldName = base.split('$')(1)
            if (segments.length > 1) {
              segments
                .slice(0, segments.length - 1)
                .foreach(seg => {
                  val elements = seg.split('$')
                  modifiedRoot = Field(root, elements(0), elements(1))
                })
            }
            Field(root, structName, fieldName)
          }
        }
      }

      case v: vpr.LocalVar =>
        v.name match {
          case "$result"                           => Result
          case temp if temp.startsWith("$result_") => ResultVar(temp)
          case id                                  => Var(id)
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
