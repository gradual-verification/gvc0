package gvc.permutation
import gvc.transformer.IR
import gvc.transformer.IR.{
  Binary,
  BinaryOp,
  Conditional,
  Expression,
  Method,
  Op,
  Predicate
}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class SelectVisitor(program: IR.Program)
    extends SpecVisitor[IR.Program, IR.Program] {
  private val predicates = mutable.ListBuffer[Predicate]()
  private val methods = mutable.ListBuffer[Method]()
  private val incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val incompleteExpr = mutable.ListBuffer[Option[IR.Expression]]()
  private val finishedExpr = mutable.ListBuffer[Option[IR.Expression]]()

  private var permutation = Set[Int]()

  override def reset(): Unit = {
    super.reset()
  }

  def visit(permutation: Set[Int]): IR.Program = {
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
      template: IR.Op,
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
      template: IR.Op
  ): Unit = {
    this.incompleteBlocks.head += template.copy
  }
  override def collectOutput(): IR.Program =
    program.copy(this.methods.toList, this.predicates.toList)

  override def collectAssertion(): Unit = {
    val assertion = this.finishedExpr.remove(0)
    if (assertion.isDefined) {
      this.incompleteBlocks.head += new IR.Assert(
        assertion.get,
        IR.AssertKind.Specification
      )
    }
  }

  override def collectIf(template: IR.If): Unit = {
    val falseBranch = this.finishedBlocks.remove(0).toList
    val trueBranch = this.finishedBlocks.remove(0).toList
    this.incompleteBlocks.head += template.copy(trueBranch, falseBranch)
  }

  override def collectWhile(whl: IR.While): Unit = {
    val invariant = new IR.Imprecise(this.finishedExpr.remove(0))
    val body = this.finishedBlocks.remove(0)
    this.incompleteBlocks.head += whl.copy(invariant, body.toList)
  }

  override def collectConditional(template: Conditional): Unit = {
    val falseBranch =
      this.finishedExpr.remove(0).getOrElse(new IR.BoolLit(true))
    val trueBranch =
      this.finishedExpr.remove(0).getOrElse(new IR.BoolLit(true))
    val resolvedConditional = Some(
      new IR.Conditional(
        template.condition,
        trueBranch,
        falseBranch
      )
    )
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
      current: Option[IR.Expression],
      toAppend: Option[IR.Expression]
  ): Option[IR.Expression] = {
    current match {
      case Some(curr) => {
        toAppend match {
          case Some(app) => {
            curr match {
              case binary: IR.Binary if binary.operator == BinaryOp.And =>
                var tempNode: IR.Binary = binary
                while (
                  tempNode.left.isInstanceOf[IR.Binary] && tempNode.left
                    .asInstanceOf[IR.Binary]
                    .operator == BinaryOp.And
                ) {
                  tempNode = tempNode.left.asInstanceOf[Binary]
                }
                tempNode.left = new IR.Binary(BinaryOp.And, app, tempNode.left)
                current
              case _ => Some(new IR.Binary(IR.BinaryOp.And, app, curr))
            }
          }
          case None => current
        }
      }
      case None =>
        toAppend match {
          case Some(_) => toAppend
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
    this.predicates += pred.copy(new IR.Imprecise(body))
  }

  override def enterMethod(method: Method): Unit = {
    this.currentContext = Some(Left(method))
  }

  override def leaveMethod(): Unit = {
    val method = this.currentContext.get.left.get
    val postcondition = Some(
      new IR.Imprecise(this.finishedExpr.remove(0))
    )
    val precondition = Some(
      new IR.Imprecise(this.finishedExpr.remove(0))
    )
    val body = this.finishedBlocks.remove(0)
    this.methods += method.copy(
      precondition,
      postcondition,
      body.toList
    )
  }
}
