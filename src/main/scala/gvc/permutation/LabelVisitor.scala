package gvc.permutation

import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Expression, Method, Predicate}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

import scala.collection.mutable

class LabelVisitor extends SpecVisitor[IRGraph.Program, List[ASTLabel]] {

  private var labelSet = mutable.ListBuffer[ASTLabel]()

  override def reset(): Unit = {
    super.reset()
    labelSet = mutable.ListBuffer[ASTLabel]()
  }

  override def visitSpec(
      parent: Either[Method, Predicate],
      template: Expression,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
  }

  override def visitSpec(
      parent: Either[Method, Predicate],
      template: IRGraph.Op,
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
  }

  def addLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    labelSet += new ASTLabel(parent, specType, exprType, this.previous())
  }
  override def visitOp(
      parent: Either[Method, Predicate],
      template: IRGraph.Op
  ): Unit = {}

  override def collectOutput(): List[ASTLabel] = { labelSet.toList }

  override def collectAssertion(): Unit = {}

  override def collectIf(template: IRGraph.If): Unit = {}

  override def collectConditional(template: IRGraph.Conditional): Unit = {}

  override def collectWhile(template: IRGraph.While): Unit = {}

  override def leaveExpr(): Unit = {}

  override def enterBlock(): Unit = {}

  override def leaveBlock(): Unit = {}

  override def enterExpr(): Unit = {}

  override def leavePredicate(): Unit = {}

  override def leaveMethod(): Unit = {}

  override def enterPredicate(predicate: Predicate): Unit = {}

  override def enterMethod(method: Method): Unit = {}
}

class ASTLabel(
    val parent: Either[Method, Predicate],
    val specType: SpecType,
    val exprType: ExprType,
    val exprIndex: Int
) {
  val hash: String = {
    val name = parent match {
      case Left(value)  => "m." + value.name
      case Right(value) => "p." + value.name
    }
    name + '.' + specType.id + '.' + exprIndex + '.' + (specType match {
      case SpecType.Postcondition => "post"
      case SpecType.Assert        => "assert"
      case SpecType.Precondition  => "pre"
      case SpecType.Unfold        => "unfold"
      case SpecType.Fold          => "fold"
      case SpecType.Predicate     => "pred"
      case SpecType.Invariant     => "inv"
    })
  }
}

object LabelOrdering extends Ordering[ASTLabel] {
  override def compare(
      x: ASTLabel,
      y: ASTLabel
  ): Int =
    x.exprIndex compare y.exprIndex
}
