package gvc.weaver
import gvc.transformer.IRGraph._
import gvc.weaver.AccessChecks.AccessTracker
import viper.silicon.Stack
import viper.silicon.state.runtimeChecks
import viper.silicon.state.BranchInfo
import viper.silver.ast.{Exp, Node}
import viper.silver.{ast => vpr}

import scala.annotation.tailrec
import scala.collection.mutable

object Weaver {
  class WeaverException(message: String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Unit =
    ir.methods.foreach { method =>
      new Weaver(method, silver.findMethod(method.name)).weave()
    }

  // Produces a list of tuples of an IR Op and its corresponding Silver statement.
  // Note that not all IR Ops produce Silver statements; the Silver statement will be
  // `None` for those Ops.
  @tailrec
  def zipOps(
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
        zipOps(irRest, vprRest, (irInvoke, Some(vprInvoke)) :: tail)
      case (
            (irAlloc: AllocValue) :: irRest,
            (vprAlloc: vpr.NewStmt) :: vprRest
          ) =>
        zipOps(irRest, vprRest, (irAlloc, Some(vprAlloc)) :: tail)
      case (
            (irAlloc: AllocStruct) :: irRest,
            (vprAlloc: vpr.NewStmt) :: vprRest
          ) =>
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

  case class Conditional(variable: Var, when: mutable.ListBuffer[Expression])

  private class Weaver(irMethod: Method, vprMethod: vpr.Method) {
    private val checks = viper.silicon.state.runtimeChecks.getChecks
    val conditions = mutable.Map[vpr.Node, mutable.Map[vpr.Exp, Conditional]]()

    val ops =
      flattenOps(irMethod.body.toList, vprMethod.body.get.ss.toList).toList

    def weave(): Unit = {
      addChecks()
      insertVersioning()
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
            conditional(assert(check.checks, returnVal), check.branch)
          )
          .foreach(insertAt(_, op))
      )
    }

    private def assert(check: vpr.Exp, returnVal: Option[Expression]): Op = {
      val checkValue =
        CheckImplementation.expression(check, irMethod, returnVal)
      new Assert(checkValue, AssertKind.Imperative)
    }

    def defineConditional(
        location: vpr.Node,
        value: vpr.Exp,
        previous: Option[Expression]
    ): Expression = {
      val (unwrapped, flag) = unwrapValue(value)
      val cond = conditions
        .getOrElseUpdate(location, mutable.ListMap())
        .getOrElseUpdate(
          unwrapped,
          Conditional(irMethod.addVar(BoolType, "_cond"), mutable.ListBuffer())
        )

      cond.when += (previous match {
        case None    => new Bool(true)
        case Some(w) => w
      })

      wrapValue(cond.variable, flag)
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

    def addVersioning(location: vpr.Node, op: Option[Op]): Unit = {
      conditions
        .get(location)
        .map(_.toSeq)
        .getOrElse(Seq.empty)
        .map {
          case (exp, cond) => {
            val value = CheckImplementation.expression(exp, irMethod, None)

            val when = cond.when.foldLeft[Option[Expression]](None) {
              (prev, c) =>
                prev match {
                  case None    => Some(c)
                  case Some(e) => Some(new Binary(BinaryOp.Or, e, c))
                }
            }

            val conditionalValue = when match {
              case None       => value
              case Some(cond) => new Binary(BinaryOp.And, cond, value)
            }

            new Assign(cond.variable, conditionalValue)
          }
        }
        .foreach(insertAt(_, op))
    }

    private def conditional(check: Op, branch: BranchInfo): Op = {
      var when: Option[Expression] = None

      (
        branch.branch,
        branch.branchOrigin,
        branch.branchPosition
      ).zipped.toSeq.reverseIterator
        .foreach {
          case (branch, origin, position) => {
            System.out.println(s"Origin: $origin, Position: $position")
            val insertAt = origin.getOrElse(position)
            val condition = defineConditional(insertAt, branch, when)

            when = when match {
              case None       => Some(condition)
              case Some(prev) => Some(new Binary(BinaryOp.And, prev, condition))
            }
          }
        }

      wrapIf(check, when)
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
