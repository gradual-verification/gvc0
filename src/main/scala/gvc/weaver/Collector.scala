
package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IRGraph._
import viper.silicon.state.BranchInfo
import viper.silver.{ast => vpr}

object Collector {
  sealed trait Location
  case class Pre(val op: Op) extends Location
  case class Post(val op: Op) extends Location
  case class Invariant(val op: Op) extends Location
  case object MethodPre extends Location
  case object MethodPost extends Location

  case class Condition(id: scala.Int, location: Location, value: CheckExpression, when: Disjunction)
  case class Conjunction(values: List[(Condition, Boolean)])
  case class Disjunction(cases: List[Conjunction])
  case class RuntimeCheck(location: Location, check: Check, when: Disjunction)
  class CollectedMethod(
    val method: Method,
    val conditions: List[Condition],
    val checks: List[RuntimeCheck],
    val returns: List[Return],
    val hasImplicitReturn: Boolean,
    val calls: List[Invoke],
    val allocations: List[Op],
  )

  class CollectedProgram(
    val program: Program,
    val methods: Map[java.lang.String, CollectedMethod]
  )

  def collect(irProgram: Program, vprProgram: vpr.Program) =
    new CollectedProgram(
      program = irProgram,
      methods = irProgram.methods
        .map(m => (m.name, new Collector(m, vprProgram.findMethod(m.name), irProgram, vprProgram).collect()))
        .toMap)

  private class ConditionTerm(val id: scala.Int) {
    val conditions = mutable.Set[Logic.Conjunction]()
  }

  private case class ViperLocation(node: Integer, child: Option[Integer])
  private object ViperLocation {
    def apply(node: vpr.Node, child: vpr.Node) =
      new ViperLocation(node.uniqueIdentifier, Some(child.uniqueIdentifier))
    def apply(node: vpr.Node) =
      new ViperLocation(node.uniqueIdentifier, None)
  }
}

class Collector(
  irMethod: Method,
  vprMethod: vpr.Method,
  irProgram: Program,
  vprProgram: vpr.Program
) {
  import Collector._

  private val viperChecks = viper.silicon.state.runtimeChecks.getChecks

  // A mapping of Viper nodes to the corresponding location in the IR.
  // This is used for locating the correct insertion of conditionals.
  private val locations = mutable.Map[ViperLocation, Location]()

  // A list of `return` statements in the IR method, used for inserting any runtime checks that
  // the postcondition may require.
  private val exits = mutable.ListBuffer[Return]()
  private val invokes = mutable.ListBuffer[Invoke]()
  private val allocations = mutable.ListBuffer[Op]()

  // The collection of conditions that are used in runtime checks. Not all conditions may be
  // necessary after simplification.
  private val conditions = mutable.Map[(Location, CheckExpression), ConditionTerm]()

  // The collection of runtime checks that are required, mapping a runtime check to the list of
  // conjuncts where one conjunct must be true in order for the runtime check to occur.
  private val checks = mutable.Map[(Location, Check), mutable.Set[Logic.Conjunction]]()

  private def visit(): Unit = {
    // Index pre-conditions and add required runtime checks
    vprMethod.pres.foreach(indexAll(_, MethodPre))
    vprMethod.pres.foreach(checkAll(_, MethodPre))

    // Loop through each operation and collect checks
    visit(irMethod.body, vprMethod.body.get)

    // Index post-conditions and add required runtime checks
    vprMethod.posts.foreach(indexAll(_, MethodPost))
    vprMethod.posts.foreach(checkAll(_, MethodPost))
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
          invokes += irInvoke
          visit(irInvoke, vprInvoke)
          vprRest
        }
        case (irAlloc: AllocValue, (vprAlloc: vpr.NewStmt) :: vprRest) => {
          allocations += irAlloc
          visit(irAlloc, vprAlloc)
          vprRest
        }
        case (irAlloc: AllocStruct, (vprAlloc: vpr.NewStmt) :: vprRest) => {
          allocations += irAlloc
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
          val cond = conditions.getOrElseUpdate((loc, unwrapped), new ConditionTerm(nextId))
          cond.conditions += conj
          
          conj & Logic.Term(cond.id, flag)
        }
      })
  }

  // TODO: pull out common factors?
  private def convertDisjunction(disjunction: Logic.Disjunction, terms: scala.Int => Condition): Disjunction =
    Disjunction(
      disjunction.conjuncts
      .toSeq
      .sorted
      .map(convertConjunction(_, terms))
      .toList)

  private def convertConjunction(conjunction: Logic.Conjunction, terms: scala.Int => Condition): Conjunction =
    Conjunction(conjunction.terms.toSeq.sorted.map(t => (terms(t.id), t.value)).toList)

  def collect(): CollectedMethod = {
    visit()

    val usedConditions = mutable.Map[scala.Int, Condition]()
    val conditionIndex = conditions.map {
      case ((loc, value), cond) => (cond.id, (loc, value, Logic.Disjunction(cond.conditions.toSet)))
    }

    def getCondition(id: scala.Int): Condition = {
      usedConditions.getOrElseUpdate(id, {
        val (loc, value, when) = conditionIndex(id)
        val simplified = Logic.simplify(when)
        val condition = convertDisjunction(simplified, getCondition(_))
        Condition(id, loc, value, condition)
      })
    }

    val collectedChecks = checks.map {
      case ((loc, check), conditions) => {
        val simplified = Logic.simplify(Logic.Disjunction(conditions.toSet))
        val condition = convertDisjunction(simplified, getCondition(_))
        RuntimeCheck(loc, check, condition)
      }
    }.toList

    new CollectedMethod(
      method = irMethod,
      conditions = usedConditions.values.toSeq.sortBy(_.id).toList,
      checks = collectedChecks,
      returns = exits.toList,
      hasImplicitReturn = hasImplicitReturn,
      calls = invokes.toList,
      allocations = allocations.toList,
    )
  }

}