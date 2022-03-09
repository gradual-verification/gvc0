package gvc.visualizer

import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{Expression, Method, Predicate}
import gvc.visualizer.ExprType.ExprType
import gvc.visualizer.SpecType.SpecType

import scala.collection.mutable

class LabelVisitor extends SpecVisitor[IRGraph.Program, List[ASTLabel]]{


  private var labelSet = mutable.ListBuffer[ASTLabel]()

  override def reset(): Unit = {
    super.reset
    labelSet = mutable.ListBuffer[ASTLabel]()
  }

  override def visitSpec(parent: Either[Method, Predicate], template: Expression, specType: SpecType, exprType: ExprType): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
  }

  override def visitSpec(parent: Either[Method, Predicate], template: IRGraph.Op, specType: SpecType, exprType: ExprType): Unit = {
    super.visitSpec(parent, template, specType, exprType)
    addLabel(parent, specType, exprType)
  }

  def addLabel(parent: Either[Method, Predicate], specType: SpecType, exprType: ExprType): Unit = {
    labelSet += new ASTLabel(parent, specType, exprType, this.specIndex)
  }
  override def visitOp(parent: Either[Method, Predicate], template: IRGraph.Op):Unit = {}

  override def collectOutput(): List[ASTLabel] = {labelSet.toList}
}

class ASTLabel(
                val parent: Either[Method, Predicate],
                val specType: SpecType,
                val exprType: ExprType,
                val exprIndex: Int,
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