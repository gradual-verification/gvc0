package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silver.{ast => vpr}

object Weaver {
  class WeaverException(message: String) extends Exception(message)

  def weave(ir: Program, silver: vpr.Program): Unit =
    new Weaver(ir, silver).weave()

  private class Weaver(ir: Program, silver: vpr.Program) {
    private sealed trait Position {
      def method: Method
      def insertBefore(op: Op): Unit
    }

    private case class AtOp(block: BasicBlock, var index: scala.Int) extends Position {
      def method = block.method

      def insertBefore(op: Op): Unit = {
        block.ops.insert(index, op)
        index += 1
      }
    }

    private case class BeforeBlock(block: Block) extends Position {
      def method = block.method

      def insertBefore(op: Op): Unit = {
        val basic = block.previous match {
          // If there is a basic block, just use that
          case Some(basic: BasicBlock) => basic
          case Some(prev) => {
            // Otherwise, insert a basic block and patch up the surrounding links
            val newBlock = new BasicBlock(block.method, Some(prev))
            newBlock.next = Some(block)

            prev.next = Some(newBlock)
            block.previous = Some(newBlock)

            newBlock
          }

          // Root blocks should always be basic blocks
          case None => throw new WeaverException("Invalid root block")
        }

        basic.ops += op
      }
    }

    def weave(): Unit = {
      ir.methods.foreach { method => weave(method, silver.findMethod(method.name)) }
    }

    private def weave(method: Method, silver: vpr.Method): Unit = {
      weave(method.entry, silver.body.get.ss.toList, silver)
    }

    private def weave(block: Block, silver: List[vpr.Stmt], silverMethod: vpr.Method): Unit = {
      val remaining = block match {
        case block: BasicBlock =>  weaveOps(block, silver, silverMethod)

        case iff: IfBlock => silver match {
          case (stmt: vpr.If) :: rest => {
            val pos = BeforeBlock(iff)
            inspect(stmt, pos)
            inspectDeep(stmt.cond, pos)

            weave(iff.ifTrue, stmt.thn.ss.toList, silverMethod)
            weave(iff.ifFalse, stmt.els.ss.toList, silverMethod)
            rest
          }
          case other => unexpected(other)
        }

        case loop: WhileBlock => silver match {
          case (stmt: vpr.While) :: rest => {
            val pos = BeforeBlock(loop)
            inspect(stmt, pos)
            inspectDeep(stmt.cond, pos)

            // TODO: Do we have runtime checks on loop invariants, and if so, where do they belong?
            stmt.invs.foreach(inspectDeep(_, pos))

            weave(loop.body, stmt.body.ss.toList, silverMethod)
            rest
          }
          case other => unexpected(other)
        }
      }

      block.next match {
        case None => remaining match {
          case Nil => ()
          case other => unexpected(other)
        }
        case Some(block) => weave(block, remaining, silverMethod)
      }
    }

    private def weaveOps(block: BasicBlock, silver: List[vpr.Stmt], silverMethod: vpr.Method): List[vpr.Stmt] = {
      var remaining = silver

      var index = 0
      while (index < block.ops.length) {
        val op = block.ops(index)
        val pos = AtOp(block, index)
        remaining = weaveOp(op, pos, remaining, silverMethod)

        // Use the index from the position, since inserting runtime checks could have modified it
        index = pos.index + 1
      }

      remaining
    }

    private def weaveOp(op: Op, pos: Position, silver: List[vpr.Stmt], silverMethod: vpr.Method): List[vpr.Stmt] = op match {
      case _: Invoke  => silver match {
        case (stmt: vpr.MethodCall) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case _: AllocValue | _ : AllocStruct => silver match {
        case (stmt: vpr.NewStmt) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case _: Assign => silver match {
        case (stmt: vpr.LocalVarAssign) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case _: AssignMember => silver match {
        case (stmt: vpr.FieldAssign) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case assert: Assert => assert.method match {
        case AssertMethod.Imperative => silver
        case AssertMethod.Specification => silver match {
          case (stmt: vpr.Assert) :: rest => {
            inspectDeep(stmt, pos)
            rest
          }
          case other => unexpected(other)
        }
      }

      case _: Fold => silver match {
        case (stmt: vpr.Fold) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case _: Unfold => silver match {
        case (stmt: vpr.Unfold) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case _: Error => silver match {
        case (stmt: vpr.Assert) :: rest => {
          inspectDeep(stmt, pos)
          rest
        }
        case other => unexpected(other)
      }

      case ret: Return => {
        val rest = ret match {
          case _: ReturnInvoke => silver match {
            case (stmt: vpr.MethodCall) :: rest => {
              // TODO: use temp variable to allow runtime checks
              inspectDeep(stmt, pos)
              rest
            }
            case other => unexpected(other)
          }

          case ret: ReturnValue => silver match {
            case (stmt: vpr.LocalVarAssign) :: rest => {
              inspectDeep(stmt, pos, Some(ret.value))
              rest
            }
            case other => unexpected(other)
          }

          case _ => silver
        }

        silverMethod.posts.foreach(inspectDeep(_, pos))
        rest
      }
    }

    private def inspect(node: vpr.Node, position: Position, returnValue: Option[Expression] = None): Unit = {
      for (check <- node.getChecks())
      for (impl <- CheckImplementation.generate(check, position.method, returnValue))
        position.insertBefore(impl)
    }

    private def inspectDeep(node: vpr.Node, position: Position, returnValue: Option[Expression] = None): Unit = {
      node.visit { case n => inspect(n, position, returnValue) }
    }

    private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
      case node :: _ => throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
      case Nil => throw new WeaverException("Expected Silver node")
    }
  }
}