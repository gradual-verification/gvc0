package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silver.{ast => vpr}

object Weaver {
  class WeaverException(message: String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Unit =
    new Weaver(ir, silver).weave()

  private class Weaver(ir: Program, silver: vpr.Program) {

    val checks = viper.silicon.state.runtimeChecks.getChecks

    def weave(): Unit = {
      ir.methods.foreach { method => weave(method, silver.findMethod(method.name)) }
    }

    private def weave(method: Method, silver: vpr.Method): Unit = {
      weave(method.body, method, silver.body.get, silver)
    }

    private def weave(block: Block, method: Method, silver: vpr.Seqn, silverMethod: vpr.Method): Unit = {
      val irOps = block.toList
      var silverOps = silver.ss.toList

      block.toList.foreach { op => silverOps = weaveOp(op, method, silverOps, silverMethod) }
      
      silverOps match {
        case Nil => ()
        case other => unexpected(other)
      }
    }

    private def weaveOp(op: Op, method: Method, silver: List[vpr.Stmt], silverMethod: vpr.Method): List[vpr.Stmt] = {
      val visit = inspectDeep(_: vpr.Node, op, method)

      op match {
        case iff: If => silver match {
          case (stmt: vpr.If) :: rest => {
            inspect(stmt, op, method)
            visit(stmt.cond)
            weave(iff.ifTrue, method, stmt.thn, silverMethod)
            weave(iff.ifFalse, method, stmt.els, silverMethod)
            rest
          }
          case other => unexpected(other)
        }

        case loop: While => silver match {
          case (stmt: vpr.While) :: rest => {
            inspect(stmt, op, method)
            visit(stmt.cond)

            // TODO: Do we have runtime checks on loop invariants, and if so, where do they belong?
            stmt.invs.foreach(visit)

            weave(loop.body, method, stmt.body, silverMethod)
            rest
          }
          case other => unexpected(other)
        }

        case _: Invoke  => silver match {
          case (stmt: vpr.MethodCall) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case _: AllocValue | _ : AllocStruct => silver match {
          case (stmt: vpr.NewStmt) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case _: AllocArray => throw new WeaverException("Unsupported array operation")

        case _: Assign => silver match {
          case (stmt: vpr.LocalVarAssign) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case _: AssignMember => silver match {
          case (stmt: vpr.FieldAssign) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case assert: Assert => assert.kind match {
          case AssertKind.Imperative => silver
          case AssertKind.Specification => silver match {
            case (stmt: vpr.Assert) :: rest => {
              visit(stmt)
              rest
            }
            case other => unexpected(other)
          }
        }

        case _: Fold => silver match {
          case (stmt: vpr.Fold) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case _: Unfold => silver match {
          case (stmt: vpr.Unfold) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case _: Error => silver match {
          case (stmt: vpr.Assert) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

        case ret: Return => {
          val rest =  ret.value match {
            case None => silver
            case Some(_) => silver match {
              case (stmt: vpr.LocalVarAssign) :: rest => {
                visit(stmt)
                rest
              }
              case other => unexpected(other)
            }
          }

          silverMethod.posts.foreach(inspectDeep(_, op, method, ret.value))
          rest
        }
      }
    }

    private def inspect(node: vpr.Node, op: Op, method: Method, returnValue: Option[Expression] = None): Unit = {
      checks.get(node).toSeq
        .flatten
        .map(_.checks)
        .flatMap(CheckImplementation.generate(_, method, returnValue))
        .foreach(op.insertBefore(_))
    }

    private def inspectDeep(node: vpr.Node, op: Op, method: Method, returnValue: Option[Expression] = None): Unit = {
      node.visit { case n => inspect(n, op, method, returnValue) }
    }

    private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
      case node :: _ => throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
      case Nil => throw new WeaverException("Expected Silver node")
    }
  }
}