package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silver.{ast => vpr}
import scala.annotation.tailrec

object Weaver {
  class WeaverException(message: String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Unit =
    new Weaver(ir, silver).weave()

  // Produces a list of tuples of an IR Op and its corresponding Silver statement.
  // Note that not all IR Ops produce Silver statements; the Silver statement will be
  // `None` for those Ops.
  @tailrec
  def zipOps(irOps: List[Op], vprOps: List[vpr.Stmt], tail: List[(Op, Option[vpr.Stmt])] = Nil): List[(Op, Option[vpr.Stmt])] =
    (irOps, vprOps) match {
      case ((irIf: If) :: irRest, (vprIf: vpr.If) :: vprRest) =>
        zipOps(irRest, vprRest, (irIf, Some(vprIf)) :: tail)
      case ((irWhile: While) :: irRest, (vprWhile: vpr.While) :: vprRest) =>
        zipOps(irRest, vprRest, (irWhile, Some(vprWhile)) :: tail)
      case ((irInvoke: Invoke) :: irRest, (vprInvoke: vpr.MethodCall) :: vprRest) =>
         zipOps(irRest, vprRest, (irInvoke, Some(vprInvoke)) :: tail)
      case ((irAlloc: AllocValue) :: irRest, (vprAlloc: vpr.NewStmt) :: vprRest) =>
         zipOps(irRest, vprRest, (irAlloc, Some(vprAlloc)) :: tail)
      case ((irAlloc: AllocStruct) :: irRest, (vprAlloc: vpr.NewStmt) :: vprRest) =>
        zipOps(irRest, vprRest, (irAlloc, Some(vprAlloc)) :: tail)
      case ((irAssign: Assign) :: irRest, (vprAssign: vpr.LocalVarAssign) :: vprRest) =>
        zipOps(irRest, vprRest, (irAssign, Some(vprAssign)) :: tail)
      case ((irAssign: AssignMember) :: irRest, (vprAssign: vpr.FieldAssign) :: vprRest) =>
        zipOps(irRest, vprRest, (irAssign, Some(vprAssign)) :: tail)
      case ((irAssert: Assert) :: irRest, vprRest) if irAssert.kind == AssertKind.Imperative =>
        zipOps(irRest, vprRest, (irAssert, None) :: tail)
      case ((irAssert: Assert) :: irRest, (vprAssert: vpr.Assert) :: vprRest) if irAssert.kind == AssertKind.Specification =>
        zipOps(irRest, vprRest, (irAssert, Some(vprAssert)) :: tail)
      case ((irFold : Fold) :: irRest, (vprFold: vpr.Fold) :: vprRest) =>
        zipOps(irRest, vprRest, (irFold, Some(vprFold)) :: tail)
      case ((irUnfold : Unfold) :: irRest, (vprUnfold: vpr.Unfold) :: vprRest) =>
        zipOps(irRest, vprRest, (irUnfold, Some(vprUnfold)) :: tail)
      case ((irError: Error) :: irRest, (vprError: vpr.Assert) :: vprRest) =>
        zipOps(irRest, vprRest, (irError, Some(vprError)) :: tail)
      case ((irReturn: Return) :: irRest, vprRest) if irReturn.value.isEmpty =>
        zipOps(irRest, vprRest, (irReturn, None) :: tail)
      case ((irReturn: Return) :: irRest, (vprReturn: vpr.LocalVarAssign) :: vprRest) =>
        zipOps(irRest, vprRest, (irReturn, Some(vprReturn)) :: tail)

      // Termination
      case (Nil, Nil) => tail

      // Errors
      case (ir, vprStmt :: _) => throw new WeaverException(s"Unexpected Silver statement: $vprStmt for $ir")
      case (ir, Nil) => throw new WeaverException("Expected Silver node")
    }

  private class Weaver(ir: Program, silver: vpr.Program) {

    val checks = viper.silicon.state.runtimeChecks.getChecks

    def weave(): Unit = {
      ir.methods.foreach { method => weave(method, silver.findMethod(method.name)) }
    }

    private def weave(irMethod: Method, vprMethod: vpr.Method): Unit = {
      weave(irMethod.body, irMethod, vprMethod.body.get, vprMethod)

      if (irMethod.returnType.isEmpty) {
        vprMethod.posts.foreach(inspectDeep(_, None, irMethod))
      }
    }

    private def weave(irBlock: Block, irMethod: Method, vprBlock: vpr.Seqn, vprMethod: vpr.Method): Unit = {
      zipOps(irBlock.toList, vprBlock.ss.toList).foreach {
        case (irIf: If, Some(vprIf: vpr.If)) => {
          inspect(vprIf, Some(irIf), irMethod)
          inspectDeep(vprIf.cond, Some(irIf), irMethod)
          weave(irIf.ifTrue, irMethod, vprIf.thn, vprMethod)
          weave(irIf.ifFalse, irMethod, vprIf.els, vprMethod)
        }

        case (irWhile: While, Some(vprWhile: vpr.While)) => {
          inspect(vprWhile, Some(irWhile), irMethod)
          inspectDeep(vprWhile.cond, Some(irWhile), irMethod)

          // TODO: Do we have runtime checks on loop invariants, and if so, where do they belong?
          vprWhile.invs.foreach(inspectDeep(_, Some(irWhile), irMethod))

          weave(irWhile.body, irMethod, vprWhile.body, vprMethod)
        }

        case (irReturn: Return, vprReturn) => {
          vprReturn.foreach(inspectDeep(_, Some(irReturn), irMethod))
          vprMethod.posts.foreach(inspectDeep(_, Some(irReturn), irMethod, irReturn.value))
        }

        case (irOp, Some(vprStmt)) =>
          inspectDeep(vprStmt, Some(irOp), irMethod)

        case (irOp, None) => ()
      }
    }

    private def inspect(node: vpr.Node, op: Option[Op], method: Method, returnValue: Option[Expression] = None): Unit = {
      checks.get(node).toSeq
        .flatten
        .map({ check =>
          val checkValue = CheckImplementation.expression(check.checks, method, returnValue)
          val checkAssert = new Assert(checkValue, AssertKind.Imperative)

          val condition = (check.branch.branch, check.branch.branchOrigin, check.branch.branchPosition)
            .zipped
            .foldLeft[Option[Expression]](None)((current, b) => b match {
              case (branch, origin, position) => {
                val exp = CheckImplementation.expression(branch, method, None)
                Some(current.map(new Binary(BinaryOp.And, _, exp)).getOrElse(exp))
              }
            })

          condition match {
            case None => checkAssert
            case Some(cond) => {
              val ifIr = new If(cond)
              ifIr.ifTrue += checkAssert
              ifIr
            }
          }
        })
        .foreach(checkOp => op match {
          case Some(op) => op.insertBefore(checkOp)
          case None => method.body += checkOp
        })
    }

    private def inspectDeep(node: vpr.Node, op: Option[Op], method: Method, returnValue: Option[Expression] = None): Unit = {
      node.visit { case n => inspect(n, op, method, returnValue) }
    }

    private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
      case node :: _ => throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
      case Nil => throw new WeaverException("Expected Silver node")
    }
  }
}