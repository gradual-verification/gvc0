package gvc.weaver
import gvc.transformer.IR
import viper.silver.{ast => vpr}
import gvc.transformer._
import viper.silver.ast
import viper.silver.ast.{AbstractLocalVar, AccessPredicate, Add, And, AnySetBinExp, AnySetCardinality, AnySetExp, AnySetUnExp, Applying, BinExp, BoolLit, CondExp, Div, DomainBinExp, DomainUnExp, EmptySeq, EmptySet, EqCmp, EqualityCmp, ExplicitSeq, ExplicitSet, ExtensionExp, FieldAccess, FieldAccessPredicate, ForPerm, ForbiddenInTrigger, FractionalPerm, FuncLikeApp, GeCmp, GtCmp, Implies, ImpreciseExp, InhaleExhaleExp, IntLit, IntPermMul, LabelledOld, LeCmp, Let, Lhs, Literal, LocationAccess, LtCmp, MagicWand, Minus, Mod, Mul, MultisetExp, NeCmp, Not, NullLit, Old, OldExp, Or, PermAdd, PermDiv, PermExp, PermGeCmp, PermGtCmp, PermLeCmp, PermLtCmp, PermMinus, PermMul, PermSub, PossibleTrigger, PredicateAccess, PredicateAccessPredicate, QuantifiedExp, RangeSeq, ResourceAccess, SeqAppend, SeqContains, SeqDrop, SeqExp, SeqIndex, SeqLength, SeqTake, SeqUpdate, SetExp, Sub, UnExp, Unfolding}
object RuntimeCheckGenerator {
  private class RuntimeCheckGeneratorException(val message: String) extends RuntimeException {
    override def getMessage(): String = message
  }
    // Generates the checks that are required for the specified node.
  def generateChecks(node: ast.Node): Seq[IR.Op] = {
    val checklist: Seq[ast.Exp] = node.getChecks()
    checklist.map(check => new IR.Op.Assert(silverToIRExpr(check).asInstanceOf[IR.Value]))
  }

  private def dne(obj: Any): Throwable = {
    new RuntimeCheckGeneratorException("An runtime check translation does not exist for " + obj.getClass.toString())
  }

  private def silverToIRExpr(exp: ast.Exp): IR.Expr = {
    exp match {
      case literal: ast.Literal => literal match {
        case IntLit(i) => new IR.Literal.Int(i.intValue())
        case lit: BoolLit => new IR.Literal.Bool(lit.value)
        case NullLit() => IR.Literal.Null
      }
      case predicate: AccessPredicate => predicate match {
        case MagicWand(left, right) => ???
        case FieldAccessPredicate(loc, perm) => ???
        case PredicateAccessPredicate(loc, perm) => ???
      }
      case exp: PermExp => ???
      case access: LocationAccess => access match {
        case FieldAccess(rcv, field) => ???
        case PredicateAccess(args, predicateName) => ???
      }
      case access: ResourceAccess => access match {
        case MagicWand(left, right) => ???
        case access: LocationAccess => ???
      }
      case CondExp(cond, thn, els) => ???
      case Unfolding(acc, body) => ???
      case binExp: BinExp => binExp match {
        case cmp: EqualityCmp => cmp match {
          case EqCmp(left, right) => new IR.Expr.Comparison(
            silverToIRExpr(left).asInstanceOf[IR.Value],
            silverToIRExpr(right).asInstanceOf[IR.Value],
            IR.ComparisonOp.Equal
          )
          case NeCmp(left, right) => new IR.Expr.Comparison(
            silverToIRExpr(left).asInstanceOf[IR.Value],
            silverToIRExpr(right).asInstanceOf[IR.Value],
            IR.ComparisonOp.NotEqual
          )
        }
        case exp: DomainBinExp => {
          val irLeft = silverToIRExpr(exp.left).asInstanceOf[IR.Value]
          val irRight = silverToIRExpr(exp.right).asInstanceOf[IR.Value]
          exp match {
            case Add(left, right) => new IR.Expr.Arithmetic(
                irLeft,
                irRight,
                IR.ArithmeticOp.Add
            )
            case Sub(left, right) => new IR.Expr.Arithmetic(
              irLeft,
              irRight,
              IR.ArithmeticOp.Subtract
            )
            case Mul(left, right) => new IR.Expr.Arithmetic(
              irLeft,
              irRight,
              IR.ArithmeticOp.Multiply
            )
            case Div(left, right) => new IR.Expr.Arithmetic(
              irLeft,
              irRight,
              IR.ArithmeticOp.Divide
            )
            case LtCmp(left, right) => new IR.Expr.Comparison(
              irLeft,
              irRight,
              IR.ComparisonOp.LessThan
            )
            case LeCmp(left, right) => new IR.Expr.Comparison(
              irLeft,
              irRight,
              IR.ComparisonOp.LessThanEqual
            )
            case GtCmp(left, right) => new IR.Expr.Comparison(
              irLeft,
              irRight,
              IR.ComparisonOp.GreaterThan
            )
            case GeCmp(left, right) => new IR.Expr.Comparison(
              irLeft,
              irRight,
              IR.ComparisonOp.GreaterThanEqual
            )
            case Or(left, right) => new IR.Expr.Logical(
              irLeft,
              irRight,
              IR.LogicalOp.Or
            )
            case And(left, right) => new IR.Expr.Logical(
              irLeft,
              irRight,
              IR.LogicalOp.And
            )
            case _ => throw dne(exp)
          }
        }
      }
      case exp: UnExp => exp match {
        case exp: OldExp => exp match {
          case Old(exp) => ???
          case LabelledOld(exp, oldLabel) => ???
        }
        case exp: DomainUnExp => exp match {
          case Minus(exp) => new IR.Expr.Negation(exp.asInstanceOf[IR.Value])
          case Not(exp) => new IR.Expr.Not(exp.asInstanceOf[IR.Value])
          case _ => throw dne(exp)
        }
      }
      case _ => throw dne(exp)
    }
  }
}