package gvc.permutation

import gvc.transformer.IR
import gvc.transformer.IR.{Expression, Method, Predicate, PredicateInstance}
import gvc.permutation.ExprType.ExprType
import gvc.permutation.SpecType.SpecType

import scala.collection.mutable

case class LabelOutput(
    labels: List[ASTLabel],
    completeMethodCounts: Map[String, Int],
    completePredicateCounts: Map[String, Int],
    methodPredicateDependencies: Map[String, mutable.Set[String]],
    predicatePredicateDependencies: Map[String, mutable.Set[String]]
)

class LabelVisitor extends SpecVisitor[IR.Program, LabelOutput] {

  val methodLabels: mutable.Map[String, Int] = mutable.Map[String, Int]()
  val predicateLabels: mutable.Map[String, Int] = mutable.Map[String, Int]()
  val methodToPredicateDependencies: mutable.Map[String, mutable.Set[String]] =
    mutable.Map[String, mutable.Set[String]]()
  val predicateToPredicateDependencies
      : mutable.Map[String, mutable.Set[String]] =
    mutable.Map[String, mutable.Set[String]]()

  var labelCount = 0

  def printCounts(labels: List[ASTLabel]) = {
    Output.info("Specification component counts: ")

    val folds = labels.filter(_.specType == SpecType.Fold)
    Output.info("Folds: " + folds.length)

    val unfolds = labels.filter(_.specType == SpecType.Unfold)
    Output.info("Unfolds: " + unfolds.length)

    val preconditions = labels.filter(_.specType == SpecType.Precondition)
    Output.info("Preconditions: " + componentTypeCounts(preconditions))

    val postconditions = labels.filter(_.specType == SpecType.Postcondition)
    Output.info("Postconditions: " + componentTypeCounts(postconditions))

    val invariants = labels.filter(_.specType == SpecType.Invariant)
    Output.info("Loop Invariants: " + componentTypeCounts(invariants))

    val pred_bodies = labels.filter(_.specType == SpecType.Predicate)
    Output.info("Predicate bodies: " + componentTypeCounts(pred_bodies))
  }

  private def componentTypeCounts(labels: List[ASTLabel]): String = {
    val pred_inst = labels.count(_.exprType == ExprType.Predicate)
    val bool_expr = labels.count(_.exprType == ExprType.Default)
    val acc = labels.count(_.exprType == ExprType.Accessibility)
    List(acc, pred_inst, bool_expr).mkString("/")
  }

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
    template match {
      case predInst: PredicateInstance =>
        parent match {
          case Left(value) =>
            methodToPredicateDependencies.getOrElseUpdate(
              value.name,
              mutable.Set.empty[String]
            ) += predInst.predicate.name
          case Right(value) =>
            if (value.name != predInst.predicate.name) {
              predicateToPredicateDependencies.getOrElseUpdate(
                value.name,
                mutable.Set.empty[String]
              ) += predInst.predicate.name
            }
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
    addLabel(parent, specType, exprType)
  }

  def addLabel(
      parent: Either[Method, Predicate],
      specType: SpecType,
      exprType: ExprType
  ): Unit = {
    labelSet += new ASTLabel(parent, specType, exprType, this.previous())
    labelCount += 1
  }

  override def visitOp(
      parent: Either[Method, Predicate],
      template: IR.Op
  ): Unit = {}

  override def collectOutput(): LabelOutput = {
    LabelOutput(
      labelSet.toList,
      methodLabels.toMap,
      predicateLabels.toMap,
      methodToPredicateDependencies.toMap,
      predicateToPredicateDependencies.toMap
    )
  }

  override def collectAssertion(): Unit = {}

  override def collectIf(template: IR.If): Unit = {}

  override def collectConditional(template: IR.Conditional): Unit = {}

  override def collectWhile(template: IR.While): Unit = {}

  override def leaveExpr(): Unit = {}

  override def enterBlock(): Unit = {}

  override def leaveBlock(): Unit = {}

  override def enterExpr(): Unit = {}

  override def leavePredicate(predicate: Predicate): Unit = {
    predicateLabels += (predicate.name -> labelCount)
    labelCount = 0
  }

  override def leaveMethod(method: Method): Unit = {
    methodLabels += (method.name -> labelCount)
    labelCount = 0
  }

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
    val specTypeName = specType match {
      case SpecType.Postcondition => "post"
      case SpecType.Assert        => "assert"
      case SpecType.Precondition  => "pre"
      case SpecType.Unfold        => "unfold"
      case SpecType.Fold          => "fold"
      case SpecType.Predicate     => "pred"
      case SpecType.Invariant     => "inv"
    }
    val exprTypeName = exprType match {
      case gvc.permutation.ExprType.Accessibility => "acc"
      case gvc.permutation.ExprType.Predicate     => "pred_inst"
      case gvc.permutation.ExprType.Default       => "default"
    }
    List(name, specType.id, specTypeName, exprTypeName, exprIndex).mkString(".")
  }
}

object LabelOrdering extends Ordering[ASTLabel] {
  override def compare(
      x: ASTLabel,
      y: ASTLabel
  ): Int =
    x.exprIndex compare y.exprIndex
}
