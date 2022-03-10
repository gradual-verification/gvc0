package gvc.visualizer

import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Conditional, Expression, Method, Op, Predicate}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.SpecType.SpecType
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class SelectVisitor(program: IRGraph.Program) extends SpecVisitor[IRGraph.Program, IRGraph.Program]{
  private val predicates = mutable.ListBuffer[Predicate]()
  private val methods = mutable.ListBuffer[Method]()
  private val incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val incompleteExpr = mutable.ListBuffer[Option[IRGraph.Expression]]()
  private val finishedExpr = mutable.ListBuffer[Option[IRGraph.Expression]]()

  private var permutationBuffer:mutable.ListBuffer[ASTLabel] = mutable.ListBuffer.empty

  override def reset(): Unit = {
    super.reset()
  }

  def visit(permutation: List[ASTLabel]): IRGraph.Program = {
    this.permutationBuffer = mutable.ListBuffer.empty[ASTLabel] ++ permutation
    super.visit(program)
  }

  override def visitSpec(parent: Either[Method, Predicate], template: Expression, specType: SpecType, exprType: ExprType): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    if (this.specIndex - 1 == this.permutationBuffer.head.exprIndex) {
      val top = this.incompleteExpr.remove(0)
      this.incompleteExpr.insert(0, mergeBinary(top, Some(template)))
    }
  }

  override def visitSpec(parent: Either[Method, Predicate], template: IRGraph.Op, specType: SpecType, exprType: ExprType): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    if(this.specIndex - 1 == this.permutationBuffer.head.exprIndex) {
      this.incompleteBlocks.head += template.copy
    }
  }

  override def visitOp(parent: Either[Method, Predicate], template: IRGraph.Op):Unit = {
    if(this.specIndex - 1 == this.permutationBuffer.head.exprIndex)
      this.incompleteBlocks.last += template.copy
  }

  override def collectOutput(): IRGraph.Program = {
    program.copy(this.methods.toList, this.predicates.toList)
  }

  override def collectAssertion(): Unit = {
    this.incompleteBlocks.head += new IRGraph.Assert(this.incompleteExpr.remove(0).get, IRGraph.AssertKind.Specification)
  }

  override def collectIf(template: IRGraph.If): Unit = {
    val falseBranch = this.finishedBlocks.remove(0).toList
    val trueBranch = this.finishedBlocks.remove(0).toList
    this.incompleteBlocks.head += template.copy(trueBranch, falseBranch)
  }

  override def collectWhile(whl: IRGraph.While): Unit = {
    val invariant = this.finishedExpr.remove(0)
    val body = this.finishedBlocks.remove(0)
    this.incompleteBlocks.head += whl.copy(invariant, body.toList)
  }

  override def collectConditional(template: Conditional): Unit = {
    val falseBranch = this.finishedExpr.remove(0)
    val trueBranch = this.finishedExpr.remove(0)

    val resolvedConditional:Option[Expression] = trueBranch match {
      case Some(tBranch) =>
        falseBranch match {
          case Some(fBranch) =>
                Some(new IRGraph.Conditional(
                  template.condition,
                  tBranch,
                  fBranch
            ))
          case None => trueBranch
        }
      case None =>
        falseBranch match {
          case Some(_) => falseBranch
          case None => None
        }
    }
    val top = this.incompleteExpr.remove(0)
    this.incompleteExpr += mergeBinary(top, resolvedConditional)
  }
  override def enterExpr(): Unit = this.incompleteExpr += None

  override def leaveExpr(): Unit =
    this.finishedExpr += this.incompleteExpr.remove(0)

  override def enterBlock(): Unit = {
    this.incompleteBlocks += new ListBuffer[Op]()
  }
  override def leaveBlock(): Unit = {
    this.finishedBlocks += this.incompleteBlocks.remove(0)
  }

  private def mergeBinary(lVal: Option[IRGraph.Expression], rVal: Option[IRGraph.Expression]): Option[IRGraph.Expression] = {
    lVal match {
    case Some(l) =>
      rVal match {
        case Some(r) =>
          Some(new IRGraph.Binary(IRGraph.BinaryOp.And,
            l, r
          ))
        case None => lVal
      }
    case None =>
      rVal match {
        case Some(_) => rVal
        case None => None
      }
  }
  }

  override def switchContext(newContext: Either[Method, Predicate]): Unit = {
    newContext match {
      case Left(method: Method) => {
        val postcondition = this.finishedExpr.remove(0)
        val precondition = this.finishedExpr.remove(0)
        val body = this.finishedBlocks.remove(0)
        this.methods += method.copy(precondition, postcondition, body.toList)
      }
      case Right(pred: Predicate) => {
        val body = this.finishedExpr.remove(0)
        this.predicates += pred.copy(body.get)
      }
    }
  }
}
