package gvc.weaver

import scala.collection.mutable.ListBuffer
import gvc.transformer.IR
import gvc.transformer.IR.Op
import viper.silver.{ast => vpr}

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
    new IR.MethodImplementation(
      c0.name,
      c0.returnType,
      c0.arguments,
      c0.precondition,
      c0.postcondition,
      c0.variables,
      new IR.Block(weaveOps(c0.body.operations, silver.body.get.ss.toList))
    )
  }

  private def unexpected(node: vpr.Node): Nothing =
    throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
  private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
    case some :: _ => unexpected(some)
    case Nil => throw new WeaverException("Expected Silver node")
  }

  private def collectChecks(node: vpr.Node): Seq[IR.Op] = {
    var checks = Seq[IR.Op]()
    val visitor: PartialFunction[vpr.Node, Unit] =  {
      case n => checks = checks ++ RuntimeCheckGenerator.generateChecks(n)
    }

    node.visit(visitor)
    checks
  }


  private def weaveOps(ops: List[IR.Op], silverNodes: List[vpr.Node]): List[IR.Op] = {
    var remaining = silverNodes
    val output = ops.flatMap({ op =>
      print(op.getClass().toString())
      val (silverOp, tail) = parseSilver(op, remaining)
      remaining = tail
      silverOp.flatMap(collectChecks) :+ op
    })
    
    remaining match {
      case node :: _ => unexpected(node) // Not all Silver nodes were consumed
      case _ => output
    }
  }

  private def parseSilver(op: IR.Op, silver: List[vpr.Node]): (Seq[vpr.Node], List[vpr.Node]) = op match {
    case op: IR.SimpleOp => op match {
      case assign: Op.AssignVar => assign.value match {
        case invoke: IR.Expr.Invoke => silver match {
          case (node: vpr.MethodCall) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
        case _ => silver match {
          case (node: vpr.LocalVarAssign) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
      }
      case member: Op.AssignMember => member.value match {
        case invoke: IR.Expr.Invoke => silver match {
          case (node: vpr.MethodCall) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
        case _ => silver match {
          case (node: vpr.FieldAssign) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
      }

      case array: Op.AssignArray => ???
      case member: Op.AssignArrayMember => ???
      case ptr: Op.AssignPtr => ???
      case assert: Op.Assert => silver match {
        case (node: vpr.Assert) :: tail => (Seq(node), tail)
        case node => unexpected(node)
      }
      case spec: Op.AssertSpec => ???
      case fold: Op.Fold => ???
      case unfold: Op.Unfold => ???
      case error: Op.Error => ???
      case ret: Op.Return => ret.value match {
        case None => (Seq.empty, silver)
        case Some(_) => silver match {
          case (node: vpr.LocalVarAssign) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
      }
      case noop: Op.Noop => noop.value match {
        case invoke: IR.Expr.Invoke => silver match {
          case (node: vpr.MethodCall) :: tail => (Seq(node), tail)
          case node => unexpected(node)
        }
        case _ => (Seq.empty, silver)
      }
    }
    case op: IR.FlowOp => op match {
      case value: Op.While => silver match {
        case (node: vpr.While) :: tail => (Seq(node), tail)
      }
      case value: Op.If => silver match {
        case (node: vpr.If) :: tail => (Seq(node), tail)
        case node => unexpected(node)
      }
    }
  }
}