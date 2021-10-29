package gvc.weaver
import gvc.transformer.IR
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

  private def unexpected(nodes: List[vpr.Node]): Nothing = nodes match {
    case node :: _ => throw new WeaverException("Encountered unexpected Silver node: " + node.toString())
    case Nil => throw new WeaverException("Expected Silver node")
  }

  private def collectChecks(node: vpr.Node): Seq[IR.Op] = {
    var checks = Seq[IR.Op]()
    val visitor: PartialFunction[vpr.Node, Unit] =  {
      case n => checks = checks ++ generateChecks(n)
    }

    node.visit(visitor)
    checks
  }

  // TODO: Implement (probably in a separate file)
  // Generates the checks that are required for the specified node.
  private def generateChecks(node: vpr.Node): Seq[IR.Op] = Seq.empty

  private def weaveOps(ops: List[IR.Op], silverNodes: List[vpr.Node]): List[IR.Op] = {
    var remaining = silverNodes
    val output = ops.flatMap({ op =>
      val (silverOp, tail) = parseSilver(op, remaining)
      remaining = tail
      silverOp.flatMap(collectChecks) :+ op
    })
    
    remaining match {
      case Nil => output
      case _ => unexpected(remaining) // Not all Silver nodes were consumed
    }
  }

  private def consume[T <: vpr.Stmt : scala.reflect.ClassTag](silver: List[vpr.Node]) = silver match {
    case t :: rest if scala.reflect.classTag[T].runtimeClass.isInstance(t) => (Seq(t), rest)
    case nodes => unexpected(nodes)
  }

  private def parseSilver(op: IR.Op, silver: List[vpr.Node]): (Seq[vpr.Node], List[vpr.Node]) = {
    op match {
      case assign: IR.Op.AssignVar => {
        assign.value match {
          case invoke: IR.Expr.Invoke => consume[vpr.MethodCall](silver)
          case alloc: IR.Expr.Alloc => consume[vpr.NewStmt](silver)
          case _ => consume[vpr.LocalVarAssign](silver)
        }
      }

      case _: IR.Op.AssignMember
        | _ : IR.Op.AssignPtr => consume[vpr.FieldAssign](silver)

      case _: IR.Op.AssignArray => ???
      case _: IR.Op.AssignArrayMember => ???

      case _: IR.Op.While => consume[vpr.While](silver)
      case _: IR.Op.If => consume[vpr.If](silver)
      case _: IR.Op.Assert => (Seq(), silver)
      case _: IR.Op.AssertSpec => consume[vpr.Assert](silver)
      case _: IR.Op.Fold => consume[vpr.Fold](silver)
      case _: IR.Op.Unfold => consume[vpr.Unfold](silver)
      case _: IR.Op.Error => consume[vpr.Assert](silver)

      case ret: IR.Op.Return => ret.value match {
        case None => (Seq.empty, silver)
        case Some(_) => consume[vpr.LocalVarAssign](silver)
      }

      case noop: IR.Op.Noop => noop.value match {
        case invoke: IR.Expr.Invoke => consume[vpr.MethodCall](silver)
        case _ => (Seq.empty, silver)
      }
    }
  }
}