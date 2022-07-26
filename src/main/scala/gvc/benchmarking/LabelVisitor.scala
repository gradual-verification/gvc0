package gvc.benchmarking

import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.SpecType.SpecType
import gvc.transformer.IR
import gvc.transformer.IR.{Expression, Method, Predicate}

import scala.collection.mutable

case class LabelOutput(
                        labels: List[ASTLabel],
                        labelsPerSpecIndex: Map[Int, Int],
                        specsToSpecIndices: Map[Expression, Int],
                        foldUnfoldCount: Map[Method, Int],
                        pairToLabelOrdering: Map[(Int, Int), Int]
                      )

class LabelVisitor extends SpecVisitor[IR.Program, LabelOutput] {

  private var labelsPerSpecIndex: mutable.Map[Int, Int] =
    mutable.Map[Int, Int]()
  private var specsToSpecIndices: mutable.Map[Expression, Int] =
    mutable.Map[Expression, Int]()
  private var foldUnfoldCount: mutable.Map[Method, Int] =
    mutable.Map[Method, Int]()
  private var labelSet = mutable.ListBuffer[ASTLabel]()

  private var startingIndex = 0

  override def reset(): Unit = {
    super.reset()
    labelSet = mutable.ListBuffer[ASTLabel]()
    foldUnfoldCount = mutable.Map[Method, Int]()
    specsToSpecIndices = mutable.Map[Expression, Int]()
    labelsPerSpecIndex = mutable.Map[Int, Int]()
    startingIndex = 0
  }

  def printCounts(labels: List[ASTLabel]): Unit = {
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
    val bool_expr = labels.count(_.exprType == ExprType.Boolean)
    val acc = labels.count(_.exprType == ExprType.Accessibility)
    val imp = labels.count(_.exprType == ExprType.Imprecision)
    List(acc, pred_inst, bool_expr, imp).mkString("/")
  }

  override def enterSpec(
                          parent: Either[Method, Predicate],
                          template: Option[Expression] = None,
                          specType: SpecType
                        ): Unit = {
    super.enterSpec(parent, template, specType)
    this.startingIndex = this.exprIndex
    template match {
      case Some(value) =>
        this.specsToSpecIndices += (value -> this.specIndex)
        specType match {
          case SpecType.Fold | SpecType.Unfold | SpecType.Assert =>
          case _ =>
            this.addLabel(
              parent,
              specType,
              ExprType.Imprecision,
              exprIndex = this.exprIndex
            )
            exprIndex += 1;
        }
      case None
        if specType == SpecType.Precondition || specType == SpecType.Postcondition =>
        this.addLabel(parent,
          specType,
          ExprType.Absent,
          exprIndex = this.exprIndex)
        exprIndex += 1;
      case _ =>
    }
  }

  override def leaveSpec(): Unit = {
    super.leaveSpec()
    labelsPerSpecIndex(this.previousSpec()) =
      if (this.previousSpec() == 0) this.exprIndex
      else
        this.exprIndex - this.startingIndex
  }

  override def visitSpecExpr(
                              parent: Either[Method, Predicate],
                              template: Expression,
                              specType: SpecType,
                              exprType: ExprType
                            ): Unit = {
    super.visitSpecExpr(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
  }

  override def visitSpecOp(
                            parent: Either[Method, Predicate],
                            template: IR.Op,
                            specType: SpecType,
                            exprType: ExprType
                          ): Unit = {
    super.visitSpecOp(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
    parent match {
      case Left(value) =>
        template match {
          case _: IR.Fold | _: IR.Unfold =>
            if (this.foldUnfoldCount.contains(value))
              this.foldUnfoldCount(value) += 1
            else
              this.foldUnfoldCount += (value -> 1)
          case _ =>
        }
      case Right(_) =>
    }
  }

  def addLabel(
                parent: Either[Method, Predicate],
                specType: SpecType.SpecType,
                exprType: ExprType.ExprType,
                exprIndex: Int = this.previousExpr()
              ): Unit = {
    val maxLong: Long = 2 * Integer.MAX_VALUE.toLong + 1
    if (labelSet.size.toLong + 1 >= maxLong) {
      throw new LabelException(
        "Maximum number of labels reached (unsigned 32-bit integer).")
    } else {
      labelSet +=
        new ASTLabel(parent, specType, exprType, this.specIndex, exprIndex)
    }
  }

  override def visitOp(
                        parent: Either[Method, Predicate],
                        template: IR.Op
                      ): Unit = {}

  override def collectOutput(): LabelOutput = {
    if (this.labelsPerSpecIndex.values.isEmpty || this.labelsPerSpecIndex.values.sum != this.labelSet.size) {
      throw new Exception(
        s"Total expression counts for each spec index don't equal the number of labels generated."
      )
    }
    LabelOutput(
      labelSet.toList,
      labelsPerSpecIndex.toMap,
      specsToSpecIndices.toMap,
      foldUnfoldCount.toMap,
      labelSet.indices
        .map(idx => {
          val l = labelSet(idx)
          ((l.specIndex, l.exprIndex), idx)
        })
        .toMap
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

  override def leavePredicate(predicate: Predicate): Unit = {}

  override def leaveMethod(method: Method): Unit = {}

  override def enterPredicate(predicate: Predicate): Unit = {}

  override def enterMethod(method: Method): Unit = {
    this.foldUnfoldCount += method -> 0
  }
}

class ASTLabel(
                val parent: Either[Method, Predicate],
                val specType: SpecType,
                val exprType: ExprType,
                val specIndex: Int,
                val exprIndex: Int
              ) {
  val hash: String = {
    val name = parent match {
      case Left(value) => "m." + value.name
      case Right(value) => "p." + value.name
    }
    List(name, specType, exprType, specIndex, exprIndex)
      .mkString(".")
  }

}
