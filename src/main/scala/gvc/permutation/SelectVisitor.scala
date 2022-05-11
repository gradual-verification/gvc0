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

class SelectVisitor(program: IR.Program)
    extends SpecVisitor[IR.Program, IR.Program] {
  private var predicates = mutable.ListBuffer[Predicate]()
  private var methods = mutable.ListBuffer[Method]()
  private var incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private var finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
  private val incompleteExpr = mutable.ListBuffer[Option[IR.Expression]]()
  private val finishedExpr = mutable.ListBuffer[Option[IR.Expression]]()

  private var permutation = Set[Int]()
  private var permutationMetadata: Option[LabelPermutation] = None

  override def reset(): Unit = {
    super.reset()
    predicates = mutable.ListBuffer[Predicate]()
    methods = mutable.ListBuffer[Method]()
    incompleteBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()
    finishedBlocks = mutable.ListBuffer[mutable.ListBuffer[Op]]()

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

  override def visitSpec(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    template match {
      case _: BoolLit => {
        this.incompleteExpr.insert(0, mergeBinary(Some(template)))
      }
      case _ if this.permutation.contains(this.previous()) => {
        this.incompleteExpr.insert(0, mergeBinary(Some(template)))
      }
      case _ =>
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

  def isComplete(method: Method): Boolean = {
    permutationMetadata match {
      case Some(value) => value.methodIsFinished(method)
      case None        => false
    }
  }

  def isComplete(predicate: Predicate): Boolean = {
    permutationMetadata match {
      case Some(value) => value.predicateIsFinished(predicate)
      case None        => false
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
    val builtInvariant = this.finishedExpr.remove(0)
    val invariant = if (isComplete(whl.method)) {
      builtInvariant match {
        case Some(value) => value
        case None        => throw new BenchmarkException("Missing conditional branch")
      }
    } else {
      new IR.Imprecise(builtInvariant)
    }
    val body = this.finishedBlocks.remove(0)
    this.incompleteBlocks.head += whl.copy(invariant, body.toList)
  }

  override def collectConditional(template: Conditional): Unit = {
    val falseBranch =
      this.finishedExpr.remove(0).getOrElse(new BoolLit(true))
    val trueBranch =
      this.finishedExpr.remove(0).getOrElse(new BoolLit(true))
    val resolvedConditional = Some(
      new IR.Conditional(
        template.condition,
        trueBranch,
        falseBranch
      )
    )
    this.incompleteExpr.insert(0, mergeBinary(resolvedConditional))
  }

  override def enterExpr(): Unit = this.incompleteExpr.insert(0, None)

  override def leaveExpr(): Unit =
    this.finishedExpr.insert(0, this.incompleteExpr.remove(0))

  override def enterBlock(): Unit =
    this.incompleteBlocks.insert(0, new ListBuffer[Op]())

  override def leaveBlock(): Unit =
    this.finishedBlocks.insert(0, this.incompleteBlocks.remove(0))

  private def mergeBinary(
      toAppend: Option[IR.Expression]
  ): Option[IR.Expression] = {
    val top = this.incompleteExpr.remove(0)
    top match {
      case Some(topExpr) => {
        toAppend match {
          case Some(app) => {
            topExpr match {
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
                top
              case _ => Some(new IR.Binary(IR.BinaryOp.And, app, topExpr))
            }
          }
          case None => top
        }
      }
      case None =>
        toAppend match {
          case Some(_) => toAppend
          case None    => None
        }
    }
  }
  override def enterPredicate(predicate: Predicate): Unit = {}
  override def leavePredicate(pred: Predicate): Unit = {
    val body = this.finishedExpr.remove(0)
    val builtPredicate = if (this.isComplete(pred)) {
      val finishedBody = body match {
        case Some(value) => value
        case None        => throw new BenchmarkException("Missing predicate body")
      }
      pred.copy(finishedBody)
    } else {
      pred.copy(new IR.Imprecise(body))
    }
    this.predicates += builtPredicate
  }

  override def enterMethod(method: Method): Unit = {}

  override def leaveMethod(method: Method): Unit = {
    val builtPostcondition = this.finishedExpr.remove(0)
    val builtPrecondition = this.finishedExpr.remove(0)
    val postcondition = if (isComplete(method)) {
      builtPostcondition match {
        case Some(value) => Some(value)
        case None        => throw new BenchmarkException("Missing postcondition")
      }
    } else {
      Some(
        new IR.Imprecise(builtPostcondition)
      )
    }
    val precondition = if (isComplete(method)) {
      builtPrecondition match {
        case Some(value) => Some(value)
        case None        => throw new BenchmarkException("Missing precondition")
      }
    } else {
      Some(
        new IR.Imprecise(builtPrecondition)
      )
    }

    val body = this.finishedBlocks.remove(0)
    this.methods += method.copy(
      precondition,
      postcondition,
      body.toList
    )
  }
}
