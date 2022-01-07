package gvc.weaver
import gvc.transformer.IRGraph._
import gvc.weaver.AccessChecks.{MethodAccessTracker, ProgramAccessTracker}
import viper.silicon.state.{BranchInfo, CheckInfo}
import viper.silver.{ast => vpr}

import scala.annotation.tailrec
import scala.collection.mutable

object Weaver {
  class WeaverException(message: java.lang.String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Boolean = {
    val tracker = new ProgramAccessTracker(ir)
    ir.methods.foreach { method =>
      val weaver = new Weaver(method, silver.findMethod(method.name))
      weaver.weave()
      tracker.register(method, weaver.tracker)
    }
    if(tracker.runtimeChecksInserted){
      tracker.injectSupport
    }
    tracker.runtimeChecksInserted
  }

  case class Conditional(id: Integer, when: mutable.ListBuffer[Logic.Conjunction])

  private class Weaver(irMethod: Method, vprMethod: vpr.Method) {
    private val checks = viper.silicon.state.runtimeChecks.getChecks
    val conditionVars = mutable.ArrayBuffer[Var]()
    val conditions = mutable.Map[vpr.Node, mutable.Map[vpr.Exp, Conditional]]()
    val tracker: MethodAccessTracker = new MethodAccessTracker(irMethod)

    val ops = flattenOps(irMethod.body.toList, vprMethod.body.get.ss.toList).toList

    def weave(): Unit = {
      addChecks()
      insertVersioning()
    }

    // Produces a list of tuples of an IR Op and its corresponding Silver statement.
    // Note that not all IR Ops produce Silver statements; the Silver statement will be
    // `None` for those Ops.
    @tailrec
    private final def zipOps(
                irOps: List[Op],
                vprOps: List[vpr.Stmt],
                tail: List[(Op, Option[vpr.Stmt])] = Nil
              ): List[(Op, Option[vpr.Stmt])] =
      (irOps, vprOps) match {
        case ((irIf: If) :: irRest, (vprIf: vpr.If) :: vprRest) =>
          zipOps(irRest, vprRest, (irIf, Some(vprIf)) :: tail)
        case ((irWhile: While) :: irRest, (vprWhile: vpr.While) :: vprRest) =>
          zipOps(irRest, vprRest, (irWhile, Some(vprWhile)) :: tail)
        case (
          (irInvoke: Invoke) :: irRest,
          (vprInvoke: vpr.MethodCall) :: vprRest
          ) =>
          tracker.invocations += irInvoke
          zipOps(irRest, vprRest, (irInvoke, Some(vprInvoke)) :: tail)
        case (
          (irAlloc: AllocValue) :: irRest,
          (vprAlloc: vpr.NewStmt) :: vprRest
          ) =>
          tracker.allocations += irAlloc
          zipOps(irRest, vprRest, (irAlloc, Some(vprAlloc)) :: tail)
        case (
          (irAlloc: AllocStruct) :: irRest,
          (vprAlloc: vpr.NewStmt) :: vprRest
          ) =>
          tracker.allocations += irAlloc
          zipOps(irRest, vprRest, (irAlloc, Some(vprAlloc)) :: tail)
        case (
          (irAssign: Assign) :: irRest,
          (vprAssign: vpr.LocalVarAssign) :: vprRest
          ) =>
          zipOps(irRest, vprRest, (irAssign, Some(vprAssign)) :: tail)
        case (
          (irAssign: AssignMember) :: irRest,
          (vprAssign: vpr.FieldAssign) :: vprRest
          ) =>
          zipOps(irRest, vprRest, (irAssign, Some(vprAssign)) :: tail)
        case ((irAssert: Assert) :: irRest, vprRest)
          if irAssert.kind == AssertKind.Imperative =>
          zipOps(irRest, vprRest, (irAssert, None) :: tail)
        case ((irAssert: Assert) :: irRest, (vprAssert: vpr.Assert) :: vprRest)
          if irAssert.kind == AssertKind.Specification =>
          zipOps(irRest, vprRest, (irAssert, Some(vprAssert)) :: tail)
        case ((irFold: Fold) :: irRest, (vprFold: vpr.Fold) :: vprRest) =>
          zipOps(irRest, vprRest, (irFold, Some(vprFold)) :: tail)
        case ((irUnfold: Unfold) :: irRest, (vprUnfold: vpr.Unfold) :: vprRest) =>
          zipOps(irRest, vprRest, (irUnfold, Some(vprUnfold)) :: tail)
        case ((irError: Error) :: irRest, (vprError: vpr.Assert) :: vprRest) =>
          zipOps(irRest, vprRest, (irError, Some(vprError)) :: tail)
        case ((irReturn: Return) :: irRest, vprRest) if irReturn.value.isEmpty =>
          zipOps(irRest, vprRest, (irReturn, None) :: tail)
        case (
          (irReturn: Return) :: irRest,
          (vprReturn: vpr.LocalVarAssign) :: vprRest
          ) =>
          tracker.returns += irReturn
          zipOps(irRest, vprRest, (irReturn, Some(vprReturn)) :: tail)

        // Termination
        case (Nil, Nil) => tail

        // Errors
        case (ir, vprStmt :: _) =>
          throw new WeaverException(
            s"Unexpected Silver statement: $vprStmt for $ir"
          )
        case (ir, Nil) => throw new WeaverException("Expected Silver node")
      }

    def flattenOps(
                    irOps: List[Op],
                    vprOps: List[vpr.Stmt]
                  ): Seq[(Op, Option[vpr.Stmt])] =
      zipOps(irOps, vprOps).toSeq.flatMap {
        case (irIf: If, Some(vprIf: vpr.If)) =>
          Seq((irIf, Some(vprIf))) ++
            flattenOps(irIf.ifTrue.toList, vprIf.thn.ss.toList) ++
            flattenOps(irIf.ifFalse.toList, vprIf.els.ss.toList)
        case (irWhile: While, Some(vprWhile: vpr.While)) =>
          Seq((irWhile, Some(vprWhile))) ++
            flattenOps(irWhile.body.toList, vprWhile.body.ss.toList)
        case (op, vprOp) => Seq((op, vprOp))
      }

    private def visit(
        visitor: (vpr.Node, Option[Op], Option[Expression]) => Unit
    ): Unit = {
      def recurse(
          node: vpr.Node,
          op: Option[Op],
          returnVal: Option[Expression]
      ) =
        node.visit { case n => visitor(n, op, returnVal) }

      ops.foreach {
        case (irIf: If, Some(vprIf: vpr.If)) => {
          visitor(vprIf, Some(irIf), None)
          recurse(vprIf.cond, Some(irIf), None)
        }

        case (irWhile: While, Some(vprWhile: vpr.While)) => {
          visitor(vprWhile, Some(irWhile), None)
          recurse(vprWhile.cond, Some(irWhile), None)

          // TODO: Where do loop invariant checks belong?
          vprWhile.invs.foreach(recurse(_, Some(irWhile), None))
        }

        case (irReturn: Return, vprReturn) => {
          vprReturn.foreach(recurse(_, Some(irReturn), None))
          vprMethod.posts.foreach(recurse(_, Some(irReturn), irReturn.value))
        }

        case (irOp, Some(vprStmt)) =>
          recurse(vprStmt, Some(irOp), None)

        case (irOp, None) => ()
      }

      if (irMethod.returnType.isEmpty) {
        vprMethod.posts.foreach(recurse(_, None, None))
      }
    }

    private def addChecks(): Unit = {
      visit((node, op, returnVal) =>
        checks
          .get(node)
          .toSeq
          .flatten
          .map(check =>
            conditional(assert(check, returnVal), check.branch)
          )
          .foreach(insertAt(_, op))
      )
    }

    private def assert(check: CheckInfo, returnVal: Option[Expression]): Op = {
        CheckImplementation.generate(check, irMethod, returnVal, tracker)
    }

    def addCondition() = {
      val i = conditionVars.length
      conditionVars += irMethod.addVar(BoolType, "_cond")
      Conditional(i, mutable.ListBuffer())
    }

    def defineConditional(
        location: vpr.Node,
        value: vpr.Exp,
        when: Logic.Conjunction
    ): Logic.Term = {
      val (unwrapped, flag) = unwrapValue(value)
      val cond = conditions
        .getOrElseUpdate(location, mutable.ListMap())
        .getOrElseUpdate(unwrapped, addCondition())

      cond.when += when
      Logic.Term(cond.id, flag)
    }

    def unwrapValue(value: vpr.Exp): (vpr.Exp, Boolean) =
      value match {
        case n: vpr.Not =>
          unwrapValue(n.exp) match {
            case (e, b) => (e, !b)
          }
        case other => (other, true)
      }

    def wrapValue(value: Expression, flag: Boolean): Expression = {
      if (flag) value
      else new Unary(UnaryOp.Not, value)
    }

    def conditionalToExpression(t: Logic.Term): Expression = wrapValue(conditionVars(t.id), t.value)
    def conditionalToExpression(conj: Logic.Conjunction): Option[Expression] =
      conj.terms.toSeq.sorted
      .foldLeft[Option[Expression]](None) { (prev, t) => prev match {
        case None => Some(conditionalToExpression(t))
        case Some(e) => Some(new Binary(BinaryOp.And, e, conditionalToExpression(t)))
      }}
    def conditionalToExpression(disj: Logic.Disjunction): Option[Expression] =
      disj.conjuncts.toSeq.sorted
      .foldLeft[Option[Expression]](None) { (prev, conj) =>
        conditionalToExpression(conj).map(conj => prev match {
          case None => conj
          case Some(e) => new Binary(BinaryOp.Or, e, conj)
        })
      }

    def addVersioning(location: vpr.Node, op: Option[Op]): Unit = {
      conditions
        .get(location)
        .map(_.toSeq)
        .getOrElse(Seq.empty)
        .map {
          case (exp, cond) => {
            val value = CheckImplementation.expression(exp, irMethod, None)
            val when = Logic.simplify(Logic.Disjunction(cond.when.toSet))
            val whenExpr = conditionalToExpression(when)
            val conditionalValue = whenExpr match {
              case None       => value
              case Some(cond) => new Binary(BinaryOp.And, cond, value)
            }

            new Assign(conditionVars(cond.id), conditionalValue)
          }
        }
        .foreach(insertAt(_, op))
    }

    private def conditional(check: Op, branch: BranchInfo): Op = {
      val when = (
        branch.branch,
        branch.branchOrigin,
        branch.branchPosition
      ).zipped.toSeq.foldRight(Logic.Conjunction())((branch, conj) => branch match {
          case (branch, origin, position) => {
            val insertAt = origin.getOrElse(position)
            conj & defineConditional(insertAt, branch, conj)
          }
        })

      wrapIf(check, conditionalToExpression(when))
    }

    private def insertVersioning(): Unit = {
      visit((node, op, returnVal) => addVersioning(node, op))
    }

    private def wrapIf(op: Op, condition: Option[Expression]) = {
      condition match {
        case None => op
        case Some(condition) => {
          val ifIr = new If(condition)
          ifIr.ifTrue += op
          ifIr
        }
      }
    }

    private def insertAt(op: Op, at: Option[Op]): Unit = at match {
      case Some(at) => at.insertBefore(op)
      case None     => irMethod.body += op
    }

  }
}
