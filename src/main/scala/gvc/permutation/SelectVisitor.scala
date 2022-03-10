package gvc.permutation
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Conditional, Expression, Method, Op, Predicate}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class SelectVisitor(program: IRGraph.Program)
    extends SpecVisitor[IRGraph.Program, IRGraph.Program] {
  private val predicates = mutable.ListBuffer[Predicate]()
  private val methods = mutable.ListBuffer[Method]()
  private val incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val incompleteExpr = mutable.ListBuffer[Option[IRGraph.Expression]]()
  private val finishedExpr = mutable.ListBuffer[Option[IRGraph.Expression]]()

  private var permutation = mutable.TreeSet[Int]()

  override def reset(): Unit = {
    super.reset()
  }

  def visit(permutation: mutable.TreeSet[Int]): IRGraph.Program = {
    this.permutation = permutation
    super.visit(program)
  }

  override def visitSpec(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    if (this.permutation.contains(this.previous())) {
      val top = this.incompleteExpr.remove(0)
      this.incompleteExpr.insert(0, mergeBinary(top, Some(template)))
    }
  }

  override def visitSpec(
      parent: Either[Method, Predicate],
      template: IRGraph.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    if (this.permutation.contains(this.previous())) {
      this.incompleteBlocks.head += template.copy
    }
  }

  override def visitOp(
      parent: Either[Method, Predicate],
      template: IRGraph.Op
  ): Unit = {
    this.incompleteBlocks.head += template.copy
  }
  override def collectOutput(): IRGraph.Program =
    program.copy(this.methods.toList, this.predicates.toList)

  override def collectAssertion(): Unit = {
    this.incompleteBlocks.head += new IRGraph.Assert(
      this.finishedExpr.remove(0).get,
      IRGraph.AssertKind.Specification
    )
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

    val resolvedConditional: Option[Expression] = trueBranch match {
      case Some(tBranch) =>
        falseBranch match {
          case Some(fBranch) =>
            Some(
              new IRGraph.Conditional(
                template.condition,
                tBranch,
                fBranch
              )
            )
          case None => trueBranch
        }
      case None =>
        falseBranch match {
          case Some(_) => falseBranch
          case None    => None
        }
    }
    val top = this.incompleteExpr.remove(0)
    this.incompleteExpr.insert(0, mergeBinary(top, resolvedConditional))
  }

  override def enterExpr(): Unit = this.incompleteExpr.insert(0, None)

  override def leaveExpr(): Unit =
    this.finishedExpr.insert(0, this.incompleteExpr.remove(0))

  override def enterBlock(): Unit =
    this.incompleteBlocks.insert(0, new ListBuffer[Op]())

  override def leaveBlock(): Unit =
    this.finishedBlocks.insert(0, this.incompleteBlocks.remove(0))

  private def mergeBinary(
      lVal: Option[IRGraph.Expression],
      rVal: Option[IRGraph.Expression]
  ): Option[IRGraph.Expression] = {
    lVal match {
      case Some(l) =>
        rVal match {
          case Some(r) =>
            Some(new IRGraph.Binary(IRGraph.BinaryOp.And, l, r))
          case None => lVal
        }
      case None =>
        rVal match {
          case Some(_) => rVal
          case None    => None
        }
    }
  }
  override def enterPredicate(predicate: Predicate): Unit = {
    this.currentContext = Some(Right(predicate))
  }
  override def leavePredicate(): Unit = {
    val pred = this.currentContext.get.right.get
    val body = this.finishedExpr.remove(0)
    this.predicates += pred.copy(new IRGraph.Imprecise(body))
  }

  override def enterMethod(method: Method): Unit = {
    this.currentContext = Some(Left(method))
  }

  override def leaveMethod(): Unit = {
    val method = this.currentContext.get.left.get
    val postcondition = Some(
      new IRGraph.Imprecise(this.finishedExpr.remove(0))
    )
    val precondition = Some(
      new IRGraph.Imprecise(this.finishedExpr.remove(0))
    )
    val body = this.finishedBlocks.remove(0)
    this.methods += method.copy(
      precondition,
      postcondition,
      body.toList
    )
  }
}
