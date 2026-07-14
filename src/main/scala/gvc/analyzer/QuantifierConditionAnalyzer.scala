package gvc.analyzer

import gvc.parser._
import scala.collection.mutable.ListBuffer

object QuantifierConditionAnalyzer {
  case class Split(
      lowerBound: ResolvedExpression,
      upperBound: ResolvedExpression,
      extraCondition: Option[ResolvedExpression]
  )

  def analyze(
      errors: ErrorSink,
      quant: BoundedQuantifiedExpression,
      qVar: ResolvedVariable,
      condition: ResolvedExpression
  ): Option[Split] = {
    def isQuantVar(expr: ResolvedExpression): Boolean =
      expr match {
        case ref: ResolvedVariableRef => ref.variable.contains(qVar)
        case _ => false
      }

    val conjuncts = flattenAnd(condition)
    val lowerMatches = ListBuffer[ResolvedExpression]()
    val upperMatches = ListBuffer[ResolvedExpression]()
    val remaining = ListBuffer[ResolvedExpression]()

    for (conjunct <- conjuncts) {
      tryLowerBound(conjunct, isQuantVar) match {
        case Some(bound) => lowerMatches += bound
        case None =>
          tryUpperBound(conjunct, isQuantVar) match {
            case Some(bound) => upperMatches += bound
            case None => remaining += conjunct
          }
      }
    }

    var ok = true

    if (lowerMatches.isEmpty) {
      errors.error(quant, s"Quantified variable ${qVar.name} is missing a lower bound")
      ok = false
    }
    if (upperMatches.isEmpty) {
      errors.error(quant, s"Quantified variable ${qVar.name} is missing an upper bound")
      ok = false
    }
    if (lowerMatches.size > 1) {
      errors.error(quant, s"Multiple lower bounds for quantified variable ${qVar.name}")
      ok = false
    }
    if (upperMatches.size > 1) {
      errors.error(quant, s"Multiple upper bounds for quantified variable ${qVar.name}")
      ok = false
    }

    if (!ok) return None

    val extraCondition =
      if (remaining.isEmpty) None
      else Resolver.combineBooleans(remaining.toSeq)

    Some(
      Split(
        lowerMatches.head,
        upperMatches.head,
        extraCondition
      )
    )
  }

  private def flattenAnd(expr: ResolvedExpression): List[ResolvedExpression] =
    expr match {
      case logical: ResolvedLogical
          if logical.operation == LogicalOperation.And =>
        flattenAnd(logical.left) ++ flattenAnd(logical.right)
      case other => List(other)
    }

  private def tryLowerBound(
      conjunct: ResolvedExpression,
      isQuantVar: ResolvedExpression => Boolean
  ): Option[ResolvedExpression] =
    conjunct match {
      case comp: ResolvedComparison =>
        comp.operation match {
          case ComparisonOperation.LessThanOrEqualTo
              if isQuantVar(comp.right) =>
            Some(comp.left)
          case ComparisonOperation.GreaterThanOrEqualTo
              if isQuantVar(comp.left) =>
            Some(comp.right)
          case _ => None
        }
      case _ => None
    }

  private def tryUpperBound(
      conjunct: ResolvedExpression,
      isQuantVar: ResolvedExpression => Boolean
  ): Option[ResolvedExpression] =
    conjunct match {
      case comp: ResolvedComparison =>
        comp.operation match {
          case ComparisonOperation.LessThan if isQuantVar(comp.left) =>
            Some(comp.right)
          case ComparisonOperation.GreaterThan if isQuantVar(comp.right) =>
            Some(comp.left)
          case _ => None
        }
      case _ => None
    }
}