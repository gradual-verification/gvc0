package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silicon.state.BranchInfo
import viper.silver.{ast => vpr}

import scala.collection.mutable

object Weaver {
  class WeaverException(message: java.lang.String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Unit = {
    ir.methods.foreach { method =>
      val weaver = new Collector(method, silver.findMethod(method.name), ir, silver)
      weaver.weave()
    }
  }

  object Collector {
    private sealed trait Location
    private case class Pre(val op: Op) extends Location
    private case class Post(val op: Op) extends Location
    private case class Invariant(val op: Op) extends Location
    private case object MethodPre extends Location
    private case object MethodPost extends Location

    private case class ViperLocation(node: Integer, child: Option[Integer])
    private object ViperLocation {
      def apply(node: vpr.Node, child: vpr.Node) =
        new ViperLocation(node.uniqueIdentifier, Some(child.uniqueIdentifier))
      def apply(node: vpr.Node) =
        new ViperLocation(node.uniqueIdentifier, None)
    }

    private class Condition(val id: scala.Int) {
      val conditions = mutable.Set[Logic.Conjunction]()
    }
  }

  private class Collector(irMethod: Method, vprMethod: vpr.Method, irProgram: Program, vprProgram: vpr.Program) {
    import Collector._

    private val viperChecks = viper.silicon.state.runtimeChecks.getChecks

    // A mapping of Viper nodes to the corresponding location in the IR.
    // This is used for locating the correct insertion of conditionals.
    private val locations = mutable.Map[ViperLocation, Location]()

    // A list of `return` statements in the IR method, used for inserting any runtime checks that
    // the postcondition may require.
    private val exits = mutable.ListBuffer[Return]()

    // The collection of conditions that are used in runtime checks. Not all conditions may be
    // necessary after simplification.
    private val conditions = mutable.Map[(Location, CheckExpression), Condition]()

    // The collection of runtime checks that are required, mapping a runtime check to the list of
    // conjuncts where one conjunct must be true in order for the runtime check to occur.
    private val checks = mutable.Map[(Location, Check), mutable.Set[Logic.Conjunction]]()

    def visit(): Unit = {
      visit(irMethod.body, vprMethod.body.get)
    }

    private def visit(irBlock: Block, vprBlock: vpr.Seqn): Unit = {
      var vprOps = vprBlock.ss.toList
      for (irOp <- irBlock) {
        vprOps = (irOp, vprOps) match {
          case (irIf: If, (vprIf: vpr.If) :: vprRest) => {
            visit(irIf, vprIf)
            visit(irIf.ifTrue, vprIf.thn)
            visit(irIf.ifFalse, vprIf.els)
            vprRest
          }
          case (irWhile: While, (vprWhile: vpr.While) :: vprRest) => {
            visit(irWhile, vprWhile)
            visit(irWhile.body, vprWhile.body)
            vprRest
          }
          case (irInvoke: Invoke, (vprInvoke: vpr.MethodCall) :: vprRest) => {
            visit(irInvoke, vprInvoke)
            vprRest
          }
          case (irAlloc: AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            visit(irAlloc, vprAlloc)
            vprRest
          }
          case (irAlloc: AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
            visit(irAlloc, vprAlloc)
            vprRest
          }
          case (irAssign: Assign, (vprAssign: vpr.LocalVarAssign) :: vprRest) => {
            visit(irAssign, vprAssign)
            vprRest
          }
          case (irAssign: AssignMember, (vprAssign: vpr.FieldAssign) :: vprRest) => {
            visit(irAssign, vprAssign)
            vprRest
          }
          case (irAssert: Assert, vprRest) if irAssert.kind == AssertKind.Imperative =>
            vprRest
          case (irAssert: Assert, (vprAssert: vpr.Assert) :: vprRest)
            if irAssert.kind == AssertKind.Specification => {
              visit(irAssert, vprAssert)
              vprRest
            }
          case (irFold: Fold, (vprFold: vpr.Fold) :: vprRest) => {
            visit(irFold, vprFold)
            vprRest
          }
          case (irUnfold: Unfold, (vprUnfold: vpr.Unfold) :: vprRest) => {
            visit(irUnfold, vprUnfold)
            vprRest
          }
          case (irError: Error, (vprError: vpr.Assert) :: vprRest) => {
            visit(irError, vprError)
            vprRest
          }
          case (irReturn: Return, vprRest) if irReturn.value.isEmpty => {
            exits += irReturn
            vprRest
          }
          case (irReturn: Return, (vprReturn: vpr.LocalVarAssign) :: vprRest) if irReturn.value.isDefined => {
            exits += irReturn
            vprRest
          }

          // Errors
          case (ir, vprStmt :: _) =>
            throw new WeaverException(s"Unexpected Silver statement: $vprStmt for $ir")
          case (_, Nil) => throw new WeaverException("Expected Silver statement")
        }
      }

      if (vprOps.nonEmpty) {
        throw new WeaverException(s"Unexpected Silver statement: ${vprOps.head}")
      }
    }

    // Combines indexing and runtime check collection for a given Viper node. Indexing must be
    // completed first, since the conditions on a runtime check may be at locations contained in
    // the same node.
    private def visit(op: Op, node: vpr.Node): Unit = {
      val loc = Pre(op)
      node match {
        case iff: vpr.If => {
          index(iff, loc)
          indexAll(iff.cond, loc)

          check(iff, loc)
          checkAll(iff.cond, loc)
        }

        case call: vpr.MethodCall => {
          val method = vprProgram.findMethod(call.methodName)
          indexAll(call, loc)
          method.pres.foreach { p =>
            p.visit { case pre => locations += ViperLocation(node, pre) -> Pre(op) }
          }
          method.posts.foreach { p =>
            p.visit { case post => locations += ViperLocation(node, post) -> Post(op) }
          }

          checkAll(call, loc)
        }

        case loop: vpr.While => {
          index(loop, loc)
          indexAll(loop.cond, loc)
          loop.invs.foreach(indexAll(_, Invariant(op)))

          check(loop, loc)
          checkAll(loop.cond, loc)
          loop.invs.foreach { i => checkAll(i, Invariant(op)) }
        }

        case n => {
          indexAll(n, loc)
          checkAll(n, loc)
        }
      }
    }

    // Adds the node to the mapping of Viper locations to IR locations
    private def index(node: vpr.Node, loc: Location): Unit =
      locations += ViperLocation(node) -> loc

    // Indexes the given node and all of its child nodes
    private def indexAll(node: vpr.Node, loc: Location): Unit =
      node.visit { case n => locations += ViperLocation(n) -> loc }

    // Finds all the runtime checks required by the given Viper node
    private def check(node: vpr.Node, loc: Location): Unit = {
      for (check <- viperChecks.get(node).toSeq.flatten) {
        val condition = branchCondition(check.branch)
        
        val returnValue = loc match {
          case Pre(ret: Return) => ret.value
          case _ => None
        }

        // TODO: Split apart ANDed checks?
        val checkValue = CheckExpression.fromViper(check.checks, irMethod, returnValue)
        checks.getOrElseUpdate((loc, checkValue), mutable.Set()) += condition
      }
    }

    // Recursively collects all runtime checks
    private def checkAll(node: vpr.Node, loc: Location): Unit =
      node.visit { case n => check(n, loc) }

    // Checks if execution can fall-through a given Op
    private def hasImplicitReturn(tailOp: Op): Boolean = tailOp match {
      case r: Return => false
      case _: While => true
      case iff: If => (iff.ifTrue.lastOption, iff.ifFalse.lastOption) match {
        case (Some(t), Some(f)) => hasImplicitReturn(t) || hasImplicitReturn(f)
        case _ => true
      }
      case _ => true
    }

    // Checks if execution can fall-through to the end of the method
    private def hasImplicitReturn: Boolean = irMethod.body.lastOption match {
      case None => true
      case Some(tailOp) => hasImplicitReturn(tailOp)
    }

    // Converts the stack of branch conditions to a logical conjunction
    private def branchCondition(branch: BranchInfo): Logic.Conjunction = {
      (branch.branch, branch.branchOrigin, branch.branchPosition)
        .zipped
        .foldRight(Logic.Conjunction())((b, conj) => b match {
          case (branch, origin, position) => {
            val vprLoc = origin match {
              case None => ViperLocation(position)
              case Some(origin) => ViperLocation(origin, position)
            }

            val loc = locations.getOrElse(vprLoc, throw new WeaverException(s"Could not find location for $origin, $position"))
            val value = CheckExpression.fromViper(branch, irMethod)
            val (unwrapped, flag) = value match {
              case CheckExpression.Not(n) => (n, false)
              case other => (other, true)
            }

            val nextId = conditions.size
            val cond = conditions.getOrElseUpdate((loc, unwrapped), new Condition(nextId))
            cond.conditions += conj
            
            conj & Logic.Term(cond.id, flag)
          }
        })
    }

    // TODO: pull out common factors?
    private def irCondition(disjunction: Logic.Disjunction, terms: scala.Int => Var): Option[Expression] =
      disjunction.conjuncts
      .foldLeft[Option[Expression]](None) { (expr, conj) =>
        irCondition(conj, terms).map(conjExpr => expr match {
          case None => conjExpr
          case Some(expr) => new Binary(BinaryOp.Or, expr, conjExpr)
        })
      }

    private def irCondition(conjunction: Logic.Conjunction, terms: scala.Int => Var): Option[Expression] =
      conjunction.terms.foldLeft[Option[Expression]](None) { (expr, term) =>
        expr match {
          case None => Some(irCondition(term, terms))
          case Some(expr) => Some(new Binary(BinaryOp.And, expr, irCondition(term, terms)))
        }
      }

    private def irCondition(term: Logic.Term, terms: scala.Int => Var): Expression =
      if (term.value) terms(term.id)
      else new Unary(UnaryOp.Not, terms(term.id))

    def weave(): Unit = {
        // Index pre-conditions and add required runtime checks
      vprMethod.pres.foreach(indexAll(_, MethodPre))
      vprMethod.pres.foreach(checkAll(_, MethodPre))

      // Loop through each operation and collect checks
      // NOTE: Ops **must not** be mutated during check collection
      visit()

      // Index post-conditions and add required runtime checks
      vprMethod.posts.foreach(indexAll(_, MethodPost))
      vprMethod.posts.foreach(checkAll(_, MethodPost))

      // Mutate the IR by adding the runtime checks and conditions
      insertChecks()
    }

    private def insertChecks(): Unit = {
      val conditionVars = mutable.Map[scala.Int, Var]()
      val conditionIndex = conditions.map {
        case ((loc, value), cond) => (cond.id, (loc, value, Logic.Disjunction(cond.conditions.toSet)))
      }

      def getCondition(id: scala.Int): Var = {
        conditionVars.get(id) match {
          case Some(v) => v
          case None => {
            // Define and add before recursing
            val newVar = irMethod.addVar(BoolType, "_cond_" + id)
            conditionVars += id -> newVar

            val (loc, value, when) = conditionIndex(id)
            val simplified = Logic.simplify(when)
            val simplifiedExpr = irCondition(simplified, getCondition(_))

            val fullExpr = simplifiedExpr match {
              case None => value.toIR(irProgram, irMethod)
              case Some(cond) => new Binary(BinaryOp.And, cond, value.toIR(irProgram, irMethod))
            }

            insertAt(loc, Seq(new Assign(newVar, fullExpr)))
            newVar
          }
        }
      }

      checks
        .map {
          case ((loc, check), conditions) => (loc, Logic.simplify(Logic.Disjunction(conditions.toSet)), check)
        }
        .groupBy {
          case (loc, cond, _) => (loc, cond)
        }
        .foreach {
          case ((loc, cond), checks) => {
            insertChecks(loc, irCondition(cond, getCondition(_)), checks.toSeq.map { case (_, _, c) => c })
          }
        }
    }

    private def generateChecks(cond: Option[Expression], checks: Seq[Check]): Seq[Op] = {
      val ops = checks.flatMap(_.toAssert(irProgram, irMethod))
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
      case MethodPre => ops.foreach(_ +=: irMethod.body)
      case MethodPost => {
        exits.foreach(e => e.insertBefore(ops))
        if (hasImplicitReturn) {
          ops.foreach(irMethod.body += _)
        }
      }
    }

    def insertChecks(at: Location, cond: Option[Expression], checks: Seq[Check]): Unit =
      insertAt(at, generateChecks(cond, checks))
  }
}
