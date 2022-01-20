package gvc.weaver

import gvc.transformer.IRGraph._
import viper.silicon.state.CheckInfo
import viper.silver.{ast => vpr}
import gvc.transformer.{IRGraphSilver}
import viper.silver.ast.{FieldAccess}

object CheckImplementation {
  def generate(
      check: CheckInfo,
      runtime: CheckRuntime,
      method: Method,
      returnValue: Option[Expression]
  ): Op = {
    check.checks match {
      /*  case vpr.FieldAccessPredicate(loc, _) =>
        assertFieldAccess(
          check,
          loc
        )*/
      case _ =>
        new Assert(
          expression(check.checks, method, returnValue),
          AssertKind.Imperative
        )
    }
  }
  def assertFieldAccess(
      check: CheckInfo,
      loc: FieldAccess
  ): Unit = {}

  def expression(
      exp: vpr.Exp,
      method: Method,
      returnValue: Option[Expression]
  ): Expression = {
    val expr = expression(_, method, returnValue)

    exp match {
      case eq: vpr.EqCmp =>
        new Binary(BinaryOp.Equal, expr(eq.left), expr(eq.right))
      case ne: vpr.NeCmp =>
        new Binary(BinaryOp.NotEqual, expr(ne.left), expr(ne.right))
      case lt: vpr.LtCmp =>
        new Binary(BinaryOp.Less, expr(lt.left), expr(lt.right))
      case lte: vpr.LeCmp =>
        new Binary(BinaryOp.LessOrEqual, expr(lte.left), expr(lte.right))
      case gt: vpr.GtCmp =>
        new Binary(BinaryOp.Greater, expr(gt.left), expr(gt.right))
      case gte: vpr.GeCmp =>
        new Binary(BinaryOp.GreaterOrEqual, expr(gte.left), expr(gte.right))

      case and: vpr.And =>
        new Binary(BinaryOp.And, expr(and.left), expr(and.right))
      case or: vpr.Or => new Binary(BinaryOp.Or, expr(or.left), expr(or.right))

      case add: vpr.Add =>
        new Binary(BinaryOp.Add, expr(add.left), expr(add.right))
      case sub: vpr.Sub =>
        new Binary(BinaryOp.Subtract, expr(sub.left), expr(sub.right))
      case mul: vpr.Mul =>
        new Binary(BinaryOp.Multiply, expr(mul.left), expr(mul.right))
      case div: vpr.Div =>
        new Binary(BinaryOp.Divide, expr(div.left), expr(div.right))

      case minus: vpr.Minus => new Unary(UnaryOp.Negate, expr(minus.exp))
      case not: vpr.Not     => new Unary(UnaryOp.Not, expr(not.exp))

      case access: vpr.FieldAccess => {
        val root = expr(access.rcv)
        val rootType = root.valueType.getOrElse(
          throw new WeaverException("Invalid root value for field access")
        )

        val fieldName = access.field.name
        rootType match {
          case ptr: PointerType => {
            // Root is a pointer, so this must be a dereference

            // Compute the field name for a dereference of this type
            val expected = ptr.valueType match {
              case BoolType           => IRGraphSilver.Names.BoolPointerValue
              case IntType | CharType => IRGraphSilver.Names.IntPointerValue
              case _: ReferenceType   => IRGraphSilver.Names.RefPointerValue
              case _ =>
                throw new WeaverException("Invalid value type for dereference")
            }

            // Check that it is the expected field name
            if (expected != fieldName)
              throw new WeaverException(
                s"Invalid dereference field: expected '$expected' but encountered '$fieldName'"
              )

            new DereferenceMember(root)
          }

          case ref: ReferenceType => {
            // Root is a struct reference, so this must be a struct member

            val structName = ref.struct.name + "$"
            val structField = ref.struct.fields
              .filter(f => structName + f.name == fieldName)
              .headOption
              .getOrElse(
                throw new WeaverException(
                  s"Could not find field $fieldName in struct ${ref.struct.name}"
                )
              )

            new FieldMember(root, structField)
          }

          case other =>
            throw new WeaverException(
              s"Cannot access member of a value with type '${other.name}'"
            )
        }
      }

      case v: vpr.LocalVar =>
        v.name match {
          case "$return" =>
            returnValue.getOrElse(
              throw new WeaverException("Invalid access to return value")
            )
          case id => method.variable(id)
        }

      case lit: vpr.BoolLit => new Bool(lit.value)
      case lit: vpr.IntLit =>
        new Int(
          lit.i.toInt
        ) // TODO: This could be used as a char type in some circumstances
      case _: vpr.NullLit => new Null()

      case e =>
        throw new WeaverException(
          "Cannot convert Silver expression `" + e.toString() + "`"
        )
    }
  }
}
