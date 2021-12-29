package gvc.weaver
import gvc.transformer.IRGraph._
import gvc.weaver.AccessChecks.AccessTracker
import viper.silicon.state.runtimeChecks
import viper.silver.{ast => vpr}

class WeaverException(message: String) extends Exception(message)

sealed trait Position {
  def method: Method
  def insertBefore(op: Op): Unit
}

class Weaver(ir: Program, silver: vpr.Program) {
  val tracker: AccessTracker = new AccessTracker()

  def weave(): Unit = {
    ir.methods.foreach { method =>
      weave(method, silver.findMethod(method.name))
    }
    AccessChecks.injectSupport(tracker)
  }

  private def weave(method: Method, silver: vpr.Method): Unit = {
    weave(method.body, method, silver.body.get, silver)
  }

  private def weave(
      block: Block,
      method: Method,
      silver: vpr.Seqn,
      silverMethod: vpr.Method
  ): Unit = {
    val irOps = block.toList
    var silverOps = silver.ss.toList
    if (method.name == "main") tracker.entry = Some(method)
    block.toList.foreach { op =>
      silverOps = weaveOp(op, method, silverOps, silverMethod)
    }

    silverOps match {
      case Nil   => ()
      case other => unexpected(other)
    }
  }

  private def weaveOp(
      op: Op,
      method: Method,
      silver: List[vpr.Stmt],
      silverMethod: vpr.Method
  ): List[vpr.Stmt] = {
    val visit = inspectDeep(_: vpr.Node, op, method)

    op match {
      case iff: If =>
        silver match {
          case (stmt: vpr.If) :: rest => {
            inspect(stmt, op, method)
            visit(stmt.cond)
            weave(iff.ifTrue, method, stmt.thn, silverMethod)
            weave(iff.ifFalse, method, stmt.els, silverMethod)
            rest
          }
          case other => unexpected(other)
        }

      case loop: While =>
        silver match {
          case (stmt: vpr.While) :: rest =>
            inspect(stmt, op, method)
            visit(stmt.cond)

            // TODO: Do we have runtime checks on loop invariants, and if so, where do they belong?
            stmt.invs.foreach(visit)

            weave(loop.body, method, stmt.body, silverMethod)
            rest
          case other => unexpected(other)
        }

      case inv: Invoke =>
        silver match {
          case (stmt: vpr.MethodCall) :: rest => {
            tracker.callGraph.addEdge(inv.method, inv, stmt, method)
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

      case _: AllocValue | _: AllocStruct =>
        silver match {
          case (stmt: vpr.NewStmt) :: rest => {
            tracker.allocations += Tuple2(method, op)
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

      case _: AllocArray =>
        throw new WeaverException("Unsupported array operation")

      case _: Assign =>
        silver match {
          case (stmt: vpr.LocalVarAssign) :: rest =>
            visit(stmt)
            rest
          case other => unexpected(other)
        }

      case _: AssignMember =>
        silver match {
          case (stmt: vpr.FieldAssign) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

      case assert: Assert =>
        assert.method match {
          case AssertMethod.Imperative => silver
          case AssertMethod.Specification =>
            silver match {
              case (stmt: vpr.Assert) :: rest =>
                visit(stmt)
                rest
              case other => unexpected(other)
            }
        }

      case _: Fold =>
        silver match {
          case (stmt: vpr.Fold) :: rest =>
            visit(stmt)
            rest
          case other => unexpected(other)
        }

      case _: Unfold =>
        silver match {
          case (stmt: vpr.Unfold) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

      case _: Error =>
        silver match {
          case (stmt: vpr.Assert) :: rest => {
            visit(stmt)
            rest
          }
          case other => unexpected(other)
        }

      case ret: Return => {
        tracker.callGraph.addReturn(ret, method)
        val (rest, value) = ret match {
          case _: ReturnInvoke =>
            silver match {
              case (stmt: vpr.MethodCall) :: rest => {
                // TODO: use temp variable to allow runtime checks
                visit(stmt)
                (rest, None)
              }
              case other => unexpected(other)
            }

          case ret: ReturnValue =>
            silver match {
              case (stmt: vpr.LocalVarAssign) :: rest => {
                visit(stmt)
                (rest, Some(ret.value))
              }
              case other => unexpected(other)
            }

          case _ => (silver, None)
        }

        silverMethod.posts.foreach(inspectDeep(_, op, method, value))
        rest
      }
    }
  }

  private def inspect(
      node: vpr.Node,
      op: Op,
      method: Method,
      returnValue: Option[Expression] = None
  ): Unit = {
    try {
      for (check <- runtimeChecks.getChecks(node))
        for (
          impl <- CheckImplementation.generate(
            check,
            method,
            returnValue,
            this.tracker
          )
        ) {
          op.insertBefore(impl)
        }
    } catch {
      case ex: NoSuchElementException => //no runtime checks present for the given Node (thrown by TrieMap)
    }
  }

  private def inspectDeep(
      node: vpr.Node,
      op: Op,
      method: Method,
      returnValue: Option[Expression] = None
  ): Unit = {
    node.visit { case n => inspect(n, op, method, returnValue) }
  }

  private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
    case node :: _ =>
      throw new WeaverException(
        "Encountered unexpected Silver node: " + node.toString()
      )
    case Nil => throw new WeaverException("Expected Silver node")
  }
}
