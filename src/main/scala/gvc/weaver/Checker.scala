package gvc.weaver

import gvc.transformer.IRGraph._
import Collector._

object Checker {
  def insert(program: CollectedProgram): Unit = {
    program.methods.values.foreach { method => new Checker(program.program, method).insert() }
  }
}

class Checker(program: Program, collected: CollectedMethod) {
  private val method = collected.method

  private val conditions = collected.conditions
    .map(cond => (cond.id, method.addVar(BoolType, s"_cond_${cond.id}")))
    .toMap

  private def getConjunction(conj: Conjunction): Option[Expression] =
    conj.values.foldLeft[Option[Expression]](None) {
      case (expr, (cond, flag)) => {
        val variable = conditions(cond.id)
        val value = if (flag) variable else new Unary(UnaryOp.Not, variable)
        expr match {
          case None => Some(value)
          case Some(expr) => Some(new Binary(BinaryOp.And, expr, value))
        }
      }
    }
  
  private def getDisjunction(disj: Disjunction): Option[Expression] =
    disj.cases.foldLeft[Option[Expression]](None) {
      case (Some(expr), conj) => getConjunction(conj).map(new Binary(BinaryOp.Or, expr, _))
      case (None, conj) => getConjunction(conj)
    }

  def insert(): Unit = {
    insertConditions()
    insertChecks()
  }

  private def insertConditions(): Unit = {
    collected.conditions.foreach { cond =>
      val variable = conditions(cond.id)
      val fullExpr = getDisjunction(cond.when) match {
        case None => cond.value.toIR(program, method)
        case Some(when) => new Binary(BinaryOp.And, when, cond.value.toIR(program, method))
      }

      insertAt(cond.location, Seq(new Assign(variable, fullExpr)))
    }
  }

  def insertChecks(): Unit = {
    collected.checks.groupBy(c => (c.location, c.when))
      .foreach {
        case ((loc, when), checks) => {
          val condition = getDisjunction(when)
          insertChecks(loc, condition, checks.map(_.check))
        }
      }
  }

  private def generateChecks(cond: Option[Expression], checks: Seq[Check]): Seq[Op] = {
    val ops = checks.flatMap(_.toAssert(program, method))
    cond match {
      case None => ops
      case Some(cond) => {
        val iff = new If(cond)
        iff.condition = cond
        ops.foreach(iff.ifTrue += _)
        Seq(iff)
      }
    }
  }

  // NOTE: Ops are call-by-name, since multiple copies of them may be necessary. DO NOT construct
  // the Ops before passing them to this method.
  private def insertAt(at: Location, ops: => Seq[Op]): Unit = at match {
    case Invariant(op) => ???
    case Pre(op) => op.insertBefore(ops)
    case Post(op) => op.insertAfter(ops)
    case MethodPre => ops.foreach(_ +=: method.body)
    case MethodPost => {
      collected.returns.foreach(e => e.insertBefore(ops))
      if (collected.hasImplicitReturn) {
        ops.foreach(method.body += _)
      }
    }
  }

  private def insertChecks(at: Location, cond: Option[Expression], checks: Seq[Check]): Unit =
    insertAt(at, generateChecks(cond, checks))
}