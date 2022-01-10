package gvc.weaver
import viper.silver.{ast => vpr}
import gvc.transformer.{IRGraph => ir}
import gvc.transformer.IRGraphSilver.Names

sealed trait Check {
  def toAssert(p: ir.Program, m: ir.Method): Seq[ir.Op]
}

sealed trait CheckExpression extends Check {
  def toIR(p: ir.Program, m: ir.Method): ir.Expression
  def getIRType(p: ir.Program, m: ir.Method): Option[ir.Type]
  def toAssert(p: ir.Program, m: ir.Method): Seq[ir.Op] = Seq(new ir.Assert(toIR(p, m), ir.AssertKind.Imperative))
}

object CheckExpression {
  type Expr = CheckExpression

  sealed trait Binary extends Expr {
    val left: CheckExpression
    val right: CheckExpression
    def op: ir.BinaryOp
    def toIR(p: ir.Program, m: ir.Method): ir.Binary = new ir.Binary(op, left.toIR(p, m), right.toIR(p, m))
  }

  sealed trait Logical extends Binary {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.BoolType)
  }
  sealed trait Comparison extends Binary {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.BoolType)
  }
  sealed trait Arithmetic extends Binary {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.IntType)
  }

  case class And(left: Expr, right: Expr) extends Logical {
    def op = ir.BinaryOp.And
  }
  case class Or(left: Expr, right: Expr) extends Logical {
    def op = ir.BinaryOp.Or
  }
  case class Add(left: Expr, right: Expr) extends Arithmetic {
    def op = ir.BinaryOp.Add
  }
  case class Sub(left: Expr, right: Expr) extends Arithmetic {
    def op = ir.BinaryOp.Subtract
  }
  case class Mul(left: Expr, right: Expr) extends Arithmetic {
    def op = ir.BinaryOp.Multiply
  }
  case class Div(left: Expr, right: Expr) extends Arithmetic {
    def op = ir.BinaryOp.Divide
  }
  case class Eq(left: Expr, right: Expr) extends Comparison {
    def op = ir.BinaryOp.Equal
  }
  case class Lt(left: Expr, right: Expr) extends Comparison {
    def op = ir.BinaryOp.Less
  }
  case class LtEq(left: Expr, right: Expr) extends Comparison {
    def op = ir.BinaryOp.LessOrEqual
  }
  case class Gt(left: Expr, right: Expr) extends Comparison {
    def op = ir.BinaryOp.Greater
  }
  case class GtEq(left: Expr, right: Expr) extends Comparison {
    def op = ir.BinaryOp.GreaterOrEqual
  }

  sealed trait UnaryCheck extends CheckExpression {
    val operand: Expr
    def op: ir.UnaryOp
    def toIR(p: ir.Program, m: ir.Method): ir.Unary = new ir.Unary(op, operand.toIR(p, m))
  }
  case class Not(operand: Expr) extends UnaryCheck {
    def op = ir.UnaryOp.Not
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.BoolType)
  }
  case class Neg(operand: Expr) extends UnaryCheck {
    def op = ir.UnaryOp.Negate
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.IntType)
  }

  case class Var(name: String) extends Expr {
    def toIR(p: ir.Program, m: ir.Method) = m.variable(name)
    def getIRType(p: ir.Program, m: ir.Method) = Some(toIR(p, m).valueType)
  }

  case class Field(root: Expr, structName: String, fieldName: String) extends Expr {
    def getIRField(p: ir.Program) =
      p.struct(structName).fields
        .find(_.name == fieldName)
        .getOrElse(throw new Weaver.WeaverException(s"Field '$fieldName' does not exist"))

    def toIR(p: ir.Program, m: ir.Method) = new ir.FieldMember(root.toIR(p, m), getIRField(p))
    def getIRType(p: ir.Program, m: ir.Method) = Some(getIRField(p).valueType)
  }

  case class Deref(operand: Expr) extends Expr {
    def toIR(p: ir.Program, m: ir.Method) = new ir.DereferenceMember(operand.toIR(p, m), getIRType(p, m).get)

    def getIRType(p: ir.Program, m: ir.Method) = operand.getIRType(p, m) match {
      case Some(ptr: ir.PointerType) => Some(ptr.valueType)
      case _ => throw new Weaver.WeaverException("Invalid dereference")
    }
  }

  sealed trait Literal extends Expr
  case class IntLit(value: Int) extends Literal {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.IntType)
    def toIR(p: ir.Program, m: ir.Method) = new ir.Int(value)
  }
  case class CharLit(value: Char) extends Literal {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.CharType)
    def toIR(p: ir.Program, m: ir.Method) = new ir.Char(value)
  }
  case class StrLit(value: String) extends Literal {
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.StringType)
    def toIR(p: ir.Program, m: ir.Method) = new ir.String(value)
  }
  case object NullLit extends Literal {
    def getIRType(p: ir.Program, m: ir.Method) = None
    def toIR(p: ir.Program, m: ir.Method) = new ir.Null()
  }
  sealed trait BoolLit extends Expr {
    def value: Boolean
    def getIRType(p: ir.Program, m: ir.Method) = Some(ir.BoolType)
    def toIR(p: ir.Program, m: ir.Method) = new ir.Bool(value)
  }
  case object TrueLit extends BoolLit {
    def value = true
  }
  case object FalseLit extends BoolLit {
    def value = false
  }

  case class Cond(cond: Expr, ifTrue: Expr, ifFalse: Expr) extends Expr {
    def toIR(p: ir.Program, m: ir.Method) = new ir.Conditional(cond.toIR(p, m), ifTrue.toIR(p, m), ifFalse.toIR(p, m))
    def getIRType(p: ir.Program, m: ir.Method) = ifTrue.getIRType(p, m).orElse(ifFalse.getIRType(p, m))
  }

  def fromIR(exp: ir.Expression): CheckExpression = {
    exp match {
      case n: ir.Var => Var(n.name)
      case n: ir.FieldMember => Field(fromIR(n.root), n.field.struct.name, n.field.name)
      case n: ir.DereferenceMember => Deref(fromIR(n.root))
      case n: ir.Int => IntLit(n.value)
      case n: ir.Char => CharLit(n.value)
      case n: ir.Bool => n.value match {
        case true => TrueLit
        case false => FalseLit
      }
      case n: ir.Null => NullLit
      case n: ir.String => StrLit(n.value)
      case n: ir.Conditional => Cond(fromIR(n.condition), fromIR(n.ifTrue), fromIR(n.ifFalse))
      case n: ir.Binary => {
        val (l, r) = (fromIR(n.left), fromIR(n.right))
        n.operator match {
          case ir.BinaryOp.Add => Add(l, r)
          case ir.BinaryOp.Subtract => Sub(l, r)
          case ir.BinaryOp.Divide => Div(l, r)
          case ir.BinaryOp.Multiply => Mul(l, r)
          case ir.BinaryOp.And => And(l, r)
          case ir.BinaryOp.Or => Or(l, r)
          case ir.BinaryOp.Equal => Eq(l, r)
          case ir.BinaryOp.NotEqual => Not(Eq(l, r))
          case ir.BinaryOp.Less => Lt(l, r)
          case ir.BinaryOp.LessOrEqual => LtEq(l, r)
          case ir.BinaryOp.Greater => Gt(l, r)
          case ir.BinaryOp.GreaterOrEqual => GtEq(l, r)
        }
      }
      case n: ir.Unary => {
        val x = fromIR(n.operand)
        n.operator match {
          case ir.UnaryOp.Negate => Neg(x)
          case ir.UnaryOp.Not => x match {
            case Not(t) => t
            case x => x
          }
        }
      }

      case _ => throw new Weaver.WeaverException("Invalid expression")
    }
  }

  def fromViper(value: vpr.Exp, method: ir.Method, returnValue: Option[ir.Expression] = None): Expr = {
    def expr(e: vpr.Exp) = fromViper(e, method, returnValue)

    value match {
      case eq: vpr.EqCmp => Eq(expr(eq.left), expr(eq.right))
      case ne: vpr.NeCmp =>  Not(Eq(expr(ne.left), expr(ne.right)))
      case lt: vpr.LtCmp => Lt(expr(lt.left), expr(lt.right))
      case lte: vpr.LeCmp => LtEq(expr(lte.left), expr(lte.right))
      case gt: vpr.GtCmp => Gt(expr(gt.left), expr(gt.right))
      case gte: vpr.GeCmp => GtEq(expr(gte.left), expr(gte.right))

      case and: vpr.And => And(expr(and.left), expr(and.right))
      case or: vpr.Or => Or(expr(or.left), expr(or.right))

      case add: vpr.Add => Add(expr(add.left), expr(add.right))
      case sub: vpr.Sub => Sub(expr(sub.left), expr(sub.right))
      case mul: vpr.Mul => Mul(expr(mul.left), expr(mul.right))
      case div: vpr.Div => Div(expr(div.left), expr(div.right))

      case minus: vpr.Minus => Neg(expr(minus.exp))
      case not: vpr.Not => expr(not.exp) match {
        case Not(f) => f
        case x => Not(x)
      }

      case access: vpr.FieldAccess => {
        val root = expr(access.rcv)
        access.field.name match {
          case Names.BoolPointerValue |
            Names.IntPointerValue |
            Names.RefPointerValue => Deref(root)
          case field => {
            val segments = field.split('$')
            if (segments.length != 2)
              throw new Weaver.WeaverException(s"Invalid field name '$field'")
            Field(root, segments(0), segments(1))
          }
        }
      }

      case v: vpr.LocalVar => v.name match {
        case "$return" => fromIR(returnValue.getOrElse(throw new Weaver.WeaverException("Invalid access to return value")))
        case id => Var(id)
      }

      case lit: vpr.BoolLit => if (lit.value) TrueLit else FalseLit
      case lit: vpr.IntLit => IntLit(lit.i.toInt) // TODO: This could be used as a char type in some circumstances
      case _: vpr.NullLit => NullLit

      case e => throw new Weaver.WeaverException("Cannot convert Silver expression `" + e.toString() + "`")
    }
  }
}