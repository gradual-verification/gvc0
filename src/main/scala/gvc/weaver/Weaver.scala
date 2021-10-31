package gvc.weaver
import gvc.transformer.IR
import viper.silver.{ast => vpr}
import scala.collection.mutable.ListBuffer

object Weaver {
  class WeaverException(val message: String) extends RuntimeException {
    override def getMessage(): String = message
  }

  def weave(c0: IR.Program, silver: vpr.Program): IR.Program = {
    new IR.Program(
      c0.methods.map {
        case impl: IR.MethodImplementation => weaveMethod(impl, findMethod(impl, silver))
        case lib: IR.LibraryMethod => lib
      },
      c0.predicates,
      c0.structs
    )
  }

  private def findMethod(method: IR.Method, program: vpr.Program) = {
    val name = "$method_" + method.name
    program.methods.filter(_.name == name).head
  }

  private def weaveMethod(c0: IR.MethodImplementation, silver: vpr.Method): IR.MethodImplementation = {
    val scope = new Scope(c0)

    def weaveBlock(input: IR.Block, verified: vpr.Seqn): IR.Block = {
      new IR.Block(weave(input.operations, verified.ss).toList)
    }

    def generateChecks(node: vpr.Node, returnValue: Option[IR.Value]): Seq[IR.Op] = {
      var ops = Seq[IR.Op]()
      val visitor: PartialFunction[vpr.Node, Unit] = {
        case n => {
          for (check <- n.getChecks()) {
            ops = ops ++ CheckImplementation.generate(check, scope, returnValue)
          }
        }
      }

      node.visit(visitor)
      ops
    }

    def weave(input: Seq[IR.Op], verified: Seq[vpr.Stmt]): ListBuffer[IR.Op] = {
      val ops = ListBuffer[IR.Op]()
      var remaining = verified.toList

      def addChecks(stmt: vpr.Stmt, returnValue: Option[IR.Value] = None): Unit = {
        ops ++= generateChecks(stmt, returnValue)
      }

      for (op <- input) {
        op match {
          case _: IR.Op.AssignVar => {
            val (stmt, rest) = remaining match {
              case (c: vpr.MethodCall) :: r => (c, r)
              case (n: vpr.NewStmt) :: r => (n, r)
              case (a: vpr.LocalVarAssign) :: r => (a, r)
              case l => unexpected(l)
            }

            remaining = rest
            addChecks(stmt)
            ops += op
          }

          case _: IR.Op.AssignMember | _: IR.Op.AssignPtr =>
            remaining match {
              case (a: vpr.FieldAssign) :: tail => {
                remaining = tail
                addChecks(a)
                ops += op
              }
              case l => unexpected(l)
            }

          case _: IR.Op.AssignArray => ???
          case _: IR.Op.AssignArrayMember => ???

          case whileOp: IR.Op.While => {
            remaining match {
              case (whileVerified: vpr.While) :: rest => {
                remaining = rest
                addChecks(whileVerified)

                ops += new IR.Op.While(
                  whileOp.condition,
                  new IR.Literal.Bool(true), // eliminate invariant
                  weaveBlock(whileOp.body, whileVerified.body))
              }

              case l => unexpected(l)
            }
          }
          case ifOp: IR.Op.If =>
            remaining match {
              case (ifVerified: vpr.If) :: rest => {
                remaining = rest
                addChecks(ifVerified)
                ops += new IR.Op.If(
                  ifOp.condition,
                  weaveBlock(ifOp.ifTrue, ifVerified.thn),
                  weaveBlock(ifOp.ifFalse, ifVerified.els))
              }
              case l => unexpected(l)
            }

          case _: IR.Op.Assert => ops += op

          case _: IR.Op.AssertSpec =>
            remaining match {
              case (assert: vpr.Assert) :: rest => {
                remaining = rest
                addChecks(assert)
                // drop specification assert but add the required dynamic checks
              }
              case l => unexpected(l)
            }

          case _: IR.Op.Fold =>
            remaining match {
              case (f: vpr.Fold) :: rest => {
                remaining = rest
                addChecks(f)
                // drop the fold but add the required dynamic checks
              }
              case l => unexpected(l)
            }

          case _: IR.Op.Unfold =>
            remaining match {
              case (uf: vpr.Unfold) :: rest => {
                remaining = rest
                addChecks(uf)
                // drop the unfold but add the required dynamic checks
              }
              case l => unexpected(l)
            }

          case _: IR.Op.Error =>
            remaining match {
              case (a: vpr.Assert) :: rest => {
                remaining = rest
                addChecks(a) // there shouldn't ever be any runtime checks
                ops += op
              }
              case l => unexpected(l)
            }

          case retOp: IR.Op.Return => {
            retOp.value match {
              case Some(value) => {
                remaining match {
                  case (assign: vpr.LocalVarAssign) :: rest => {
                    remaining = rest
                    // Will there ever be a dynamic check that refers to the return value here?
                    // It seems that a local var assign would not result in a check for the result value
                    addChecks(assign, returnValue = retOp.value)
                  }
                  case l => unexpected(l)
                }
              }

              // If no return value, no Silver code is emitted
              case None => ()
            }

            // Check post conditions
            for (post <- silver.posts) {
              ops ++= generateChecks(post, returnValue = retOp.value)
            }

            ops += retOp
          }

          case noop: IR.Op.Noop => {
            noop.value match {
              case call: IR.Expr.Invoke => {
                remaining match {
                  case (callVerified: vpr.MethodCall) :: rest => {
                    remaining = rest
                    addChecks(callVerified)
                    ops += noop
                  }

                  case l => unexpected(l)
                }
              }

              case _ => () // drop other noops
            }
          }
        }
      }

      if (!remaining.isEmpty)
        unexpected(remaining)

      ops
    }

    // Check the return type of the function
    val body = weave(c0.body.operations, silver.body.get.ss)
    c0.returnType match {
      // If the method does not have a return type, the postcondition cannot refer to
      // the return value, so we can insert the dynamic checks at the tail without having
      // a return statment.
      case None => {
        for (post <- silver.posts) {
          body ++= generateChecks(post, returnValue = None)
        }
      }

      // If method has a return type, it will need to return a value, so the postcondition
      // checks will be inserted at the return location where we can access the return value
      case Some(_) => ()
    }

    new IR.MethodImplementation(
      c0.name,
      c0.returnType,
      c0.arguments,
      new IR.Literal.Bool(true), // drop precondition
      new IR.Literal.Bool(true), // drop postcondition
      scope.getVars(),
      new IR.Block(body.toList)
    )
  }

  private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
    case node :: _ => throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
    case Nil => throw new WeaverException("Expected Silver node")
  }
}