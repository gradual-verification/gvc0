package gvc.permutation
import gvc.permutation.Bench.BenchmarkException
import gvc.transformer.IR
import gvc.transformer.IR.{
  Binary,
  BinaryOp,
  BoolLit,
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

case class BuiltExpression(componentCount: Int, expr: Option[Expression])

class SelectVisitor(program: IR.Program)
    extends SpecVisitor[IR.Program, IR.Program] {
  private var predicates = mutable.ListBuffer[Predicate]()
  private var methods = mutable.ListBuffer[Method]()
  private var incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private var finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private var incompleteExpr = mutable.ListBuffer[BuiltExpression]()
  var finishedExpr = mutable.ListBuffer[BuiltExpression]()

  private var permutation = Set[Int]()
  private var permutationMetadata: Option[LabelPermutation] = None

  override def reset(): Unit = {
    super.reset()
    predicates = mutable.ListBuffer[Predicate]()
    methods = mutable.ListBuffer[Method]()
    incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
    finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
    incompleteExpr = mutable.ListBuffer[BuiltExpression]()
    finishedExpr = mutable.ListBuffer[BuiltExpression]()
    permutation = Set.empty[Int]
    permutationMetadata = None
  }

  def visit(permutation: LabelPermutation): IR.Program = {
    super.reset()
    this.permutation = permutation.indices
    this.permutationMetadata = Some(permutation)
    super.visit(program)
  }

  def visitEmpty(): IR.Program = {
    super.reset()
    this.permutation = Set.empty
    super.visit(program)
  }

  override def enterSpec(parent: Either[Method, Predicate],
                         template: Option[Expression] = None,
                         specType: SpecType): Unit = {
    super.enterSpec(parent, template, specType)
  }

  override def visitSpecExpr(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpecExpr(parent, template, specType, exprType)
    template match {
      case _: BoolLit =>
        this.incompleteExpr.insert(0, mergeBinary(Some(template)))
      case _ if this.permutation.contains(this.previousExpr()) =>
        this.incompleteExpr.insert(0, mergeBinary(Some(template)))
      case _ =>
    }
  }

  override def visitSpecOp(
      parent: Either[Method, Predicate],
      template: IR.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpecOp(parent, template, specType, exprType)
    if (this.permutation.contains(this.previousExpr())) {
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
    val assertion = this.finishedExpr.remove(0).expr
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
    val builtInvariant = this.finishedExpr.remove(0)
    val invariant =
      if (isComplete(Some(whl.invariant))) {
        builtInvariant.expr match {
          case Some(value) => value
          case None =>
            throw new BenchmarkException("Missing conditional branch")
        }
      } else {
        new IR.Imprecise(builtInvariant.expr)
      }
    val body = this.finishedBlocks.remove(0)
    this.incompleteBlocks.head += whl.copy(invariant, body.toList)
  }

  override def collectConditional(template: Conditional): Unit = {
    val builtFalseBranch =
      this.finishedExpr.remove(0)
    val falseBranchExpr = builtFalseBranch.expr.getOrElse(new BoolLit(true))

    val builtTrueBranch =
      this.finishedExpr.remove(0)
    val trueBranchExpr = builtTrueBranch.expr.getOrElse(new BoolLit(true))

    val resolvedConditional = Some(
      new IR.Conditional(
        template.condition,
        trueBranchExpr,
        falseBranchExpr
      )
    )

    this.incompleteExpr.insert(
      0,
      mergeBinary(
        resolvedConditional,
        builtTrueBranch.componentCount + builtFalseBranch.componentCount))
  }

  override def enterExpr(): Unit =
    this.incompleteExpr.insert(0, BuiltExpression(0, None))

  override def leaveExpr(): Unit =
    this.finishedExpr.insert(0, this.incompleteExpr.remove(0))

  override def enterBlock(): Unit =
    this.incompleteBlocks.insert(0, new ListBuffer[Op]())

  override def leaveBlock(): Unit =
    this.finishedBlocks.insert(0, this.incompleteBlocks.remove(0))

  private def mergeBinary(
      toAppend: Option[IR.Expression],
      size: Int = 1
  ): BuiltExpression = {
    val builtTop = this.incompleteExpr.remove(0)
    val top = builtTop.expr
    val combined = top match {
      case Some(topExpr) =>
        toAppend match {
          case Some(app) =>
            topExpr match {
              case binary: IR.Binary if binary.operator == BinaryOp.And =>
                var tempNode: IR.Binary = binary
                while (tempNode.left.isInstanceOf[IR.Binary] && tempNode.left
                         .asInstanceOf[IR.Binary]
                         .operator == BinaryOp.And) {
                  tempNode = tempNode.left.asInstanceOf[Binary]
                }
                tempNode.left = new IR.Binary(BinaryOp.And, app, tempNode.left)
                top
              case _ => Some(new IR.Binary(IR.BinaryOp.And, app, topExpr))
            }

          case None => top
        }
      case None =>
        toAppend match {
          case Some(_) => toAppend
          case None    => None
        }
    }
    BuiltExpression(builtTop.componentCount + size, combined)
  }

  override def enterPredicate(predicate: Predicate): Unit = {}
  override def leavePredicate(pred: Predicate): Unit = {
    val body = this.finishedExpr.remove(0)
    val bodyIsComplete = body.expr match {
      case Some(_) =>
        this.permutationMetadata match {
          case Some(meta) =>
            meta.exprIsComplete(pred.expression)
          case None => false
        }
      case None => false
    }
    val builtPredicate = if (bodyIsComplete) {
      val finishedBody = body.expr match {
        case Some(value) => value
        case None        => throw new BenchmarkException("Missing predicate body")
      }
      pred.copy(finishedBody)
    } else {
      pred.copy(new IR.Imprecise(body.expr))
    }
    this.predicates += builtPredicate
    if (finishedExpr.nonEmpty) {
      throw new Exception("Not all expressions processed!")
    }
  }

  override def enterMethod(method: Method): Unit = {}

  override def leaveMethod(method: Method): Unit = {
    val builtPostcondition = this.finishedExpr.remove(0)
    val builtPrecondition = this.finishedExpr.remove(0)
    val postcondition =
      if (isComplete(method.postcondition)) {
        builtPostcondition.expr match {
          case Some(value) => Some(value)
          case None        => throw new BenchmarkException("Missing postcondition")
        }
      } else {
        if (method.postcondition.nonEmpty)
          Some(
            new IR.Imprecise(builtPostcondition.expr)
          )
        else
          None
      }
    val precondition =
      if (isComplete(method.precondition)) {
        builtPrecondition.expr match {
          case Some(value) => Some(value)
          case None        => throw new BenchmarkException("Missing precondition")
        }
      } else {
        if (method.precondition.nonEmpty)
          Some(
            new IR.Imprecise(builtPrecondition.expr)
          )
        else
          None
      }

    val body = this.finishedBlocks.remove(0)
    this.methods += method.copy(
      precondition,
      postcondition,
      body.toList
    )
    if (finishedExpr.nonEmpty) {
      throw new Exception("Not all expressions processed!")
    }
  }

  def isComplete(template: Option[Expression]): Boolean = {
    template match {
      case Some(expression) =>
        this.permutationMetadata match {
          case Some(meta) =>
            meta.exprIsComplete(expression)
          case None => false
        }
      case None => false
    }
  }
}
