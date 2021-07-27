package gvc.transformer
import scala.collection.mutable
import viper.silver.{ast => vpr}

object SilverOutput {
  def expression(scope: LocalScope, expr: IR.Expr): vpr.Exp = {
    expr match {
      case v: IR.Var => scope.localVar(v)
      case str: IR.Literal.String => ???
      case i: IR.Literal.Int => vpr.IntLit(BigInt(i.value))()
      case _: IR.Literal.Char => ???
      case b: IR.Literal.Bool => vpr.BoolLit(b.value)()
      case IR.Literal.Null => vpr.NullLit()()
      case arith: IR.Expr.Arithmetic => {
        val left = expression(scope, arith.left)
        val right = expression(scope, arith.right)
        arith.op match {
          case IR.ArithmeticOp.Add => vpr.Add(left, right)()
          case IR.ArithmeticOp.Subtract => vpr.Sub(left, right)()
          case IR.ArithmeticOp.Multiply => vpr.Mul(left, right)()
          case IR.ArithmeticOp.Divide => vpr.Div(left, right)()
        }
      }

      case comp: IR.Expr.Comparison => {
        val left = expression(scope, comp.left)
        val right = expression(scope, comp.right)
        comp.op match {
          case IR.ComparisonOp.Equal => vpr.EqCmp(left, right)()
          case IR.ComparisonOp.NotEqual => vpr.NeCmp(left, right)()
          case IR.ComparisonOp.LessThan => vpr.LtCmp(left, right)()
          case IR.ComparisonOp.LessThanEqual => vpr.LeCmp(left, right)()
          case IR.ComparisonOp.GreaterThan => vpr.GtCmp(left, right)()
          case IR.ComparisonOp.GreaterThanEqual => vpr.GeCmp(left, right)()
        }
      }

      case log: IR.Expr.Logical => {
        val left = expression(scope, log.left)
        val right = expression(scope, log.right)
        log.op match {
          case IR.LogicalOp.And => vpr.And(left, right)()
          case IR.LogicalOp.Or => vpr.Or(left, right)()
        }
      }

      case _: IR.Expr.ArrayAccess => ???
      case _: IR.Expr.ArrayFieldAccess => ???

      case deref: IR.Expr.Deref => {
        // TODO: Handle all pointer types
        vpr.FieldAccess(expression(scope, deref.subject), scope.intPtrValue)()
      }

      case negate: IR.Expr.Negation => vpr.Minus(expression(scope, negate.value))()
      case not: IR.Expr.Not => vpr.Not(expression(scope, not.value))()
      case member: IR.Expr.Member => ???
      case _: IR.Expr.Alloc => ???
      case _: IR.Expr.AllocArray => ???

      // Invokes are handled at the statement level
      case invoke: IR.Expr.Invoke => throw new TransformerException("Invalid invoke encoutered as expression")
    }
  }

  def operation(scope: LocalScope, op: IR.Op): Seq[vpr.Stmt] = {
    op match {
      case assign: IR.Op.AssignVar => {
        assign.value match {
          case invoke: IR.Expr.Invoke => {
            Seq(vpr.MethodCall(
              scope.methodName(invoke.methodName),
              invoke.arguments.map(expression(scope, _)),
              Seq(scope.localVar(assign.subject)))(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos))
          }

          case _ => {
            Seq(vpr.LocalVarAssign(scope.localVar(assign.subject), expression(scope, assign.value))())
          }
        }
      }

      case assign: IR.Op.AssignMember => {
        Seq(vpr.FieldAssign(
          vpr.FieldAccess(
            scope.localVar(assign.subject),
            scope.structField(assign.field)
          )(),
          expression(scope, assign.value)
        )())
      }

      case _: IR.Op.AssignArray => ???
      case _: IR.Op.AssignArrayMember => ???

      case assign: IR.Op.AssignPtr => {
        // TODO: Support more pointer types
        Seq(vpr.FieldAssign(vpr.FieldAccess(scope.localVar(assign.subject), scope.intPtrValue)(), expression(scope, assign.value))())
      }

      case whil: IR.Op.While => {
        // TODO: Transform invariants
        Seq(vpr.While(expression(scope, whil.condition), Seq(), block(scope, whil.body))())
      }

      case iff: IR.Op.If => {
        Seq(vpr.If(expression(scope, iff.condition), block(scope, iff.ifTrue), block(scope, iff.ifFalse))())
      }

      case assert: IR.Op.Assert => {
        Seq(vpr.Assert(expression(scope, assert.value))())
      }

      case error: IR.Op.Error => {
        // Error => assert(false)
        Seq(vpr.Assert(vpr.BoolLit(false)())())
      }

      case ret: IR.Op.Return => {
        // Since return is translated to a simple assign with no control flow branching, all returns
        // must be in the tail position
        ret.value match {
          case None => Seq() // A return with no value is ignored
          case Some(value) => Seq(vpr.LocalVarAssign(scope.returnVar, expression(scope, value))())
        }
      }

      case noop: IR.Op.Noop => {
        noop.value match {
          // Transform method calls
          case invoke: IR.Expr.Invoke => {
            Seq(vpr.MethodCall(scope.methodName(invoke.methodName), invoke.arguments.map(expression(scope, _)), Seq())(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos))
          }

          // Ignore other noops
          case _ => Seq()
        }
      }
    }
  }

  def block(scope: LocalScope, block: IR.Block, decls: Seq[vpr.Declaration] = Seq.empty): vpr.Seqn = {
    vpr.Seqn(block.operations.flatMap(operation(scope, _)), decls)()
  }

  def spec(scope: LocalScope, specification: IR.Spec): vpr.Exp = {
    specification match {
      case bool: IR.Literal.Bool => vpr.BoolLit(bool.value)()
      case int: IR.Literal.Int => vpr.IntLit(BigInt(int.value))()

      case arg: IR.Spec.ArgumentValue => scope.localVar(arg.argument)

      case ret: IR.Spec.ReturnValue => scope.returnVar

      case comp: IR.Spec.Comparison => {
        val left = spec(scope, comp.left)
        val right = spec(scope, comp.right)
        comp.op match {
          case IR.ComparisonOp.Equal => vpr.EqCmp(left, right)()
          case IR.ComparisonOp.NotEqual => vpr.NeCmp(left, right)()
          case IR.ComparisonOp.LessThan => vpr.LtCmp(left, right)()
          case IR.ComparisonOp.LessThanEqual => vpr.LeCmp(left, right)()
          case IR.ComparisonOp.GreaterThan => vpr.GtCmp(left, right)()
          case IR.ComparisonOp.GreaterThanEqual => vpr.GeCmp(left, right)()
        }
      }

      case conjunction: IR.Spec.Conjunction => {
        val left = spec(scope, conjunction.left)
        val right = spec(scope, conjunction.right)
        vpr.And(left, right)()
      }

      case conditional: IR.Spec.Conditional => {
        val condition = spec(scope, conditional.condition)
        val left = spec(scope, conditional.ifTrue)
        val right = spec(scope, conditional.ifTrue)
        vpr.CondExp(condition, left, right)()
      }
    }
  }

  def method(scope: GlobalScope, impl: IR.MethodImplementation): vpr.Method = {
    def declareVar(variable: IR.Var): vpr.LocalVarDecl =
      vpr.LocalVarDecl(variable.name, getType(scope, variable.varType))()

    val returnValue = impl.returnType.map(t => vpr.LocalVarDecl("$return", getType(scope, t))())
    val formalArgs = impl.arguments.map(arg => (arg, declareVar(arg)))
    val variables = impl.variables.map(v => (v, declareVar(v)))

    val scopedVars = (formalArgs.toSeq ++ variables.toSeq).toMap

    val localScope = scope.local(returnValue, scopedVars)
    val body = block(localScope, impl.body, variables.map({ case (_, decl) => decl }))
    val precondition = spec(localScope, impl.precondition)
    val postcondition = spec(localScope, impl.postcondition)

    vpr.Method(
      scope.methodName(impl.name),
      formalArgs.map({ case (_, decl) => decl }),
      returnValue.toSeq,
      Seq(precondition), Seq(postcondition),
      Some(body))()
  }

  def program(program: IR.Program): vpr.Program = {
    val scope = new GlobalScope()
    val methods = program.methods.collect { case impl: IR.MethodImplementation => impl }
      .map(method(scope, _))
      .toList

    val fields = scope.fields.toList

    vpr.Program(
      domains = Seq.empty,
      fields = fields,
      functions = Seq.empty,
      predicates = Seq.empty,
      methods = methods,
      extensions = Seq.empty
    )()
  }

  def getType(scope: GlobalScope, t: IR.Type): vpr.Type = {
    t match {
      case IR.Type.Array(_) => ???
      case IR.Type.StructReference(_, _) => ???
      case IR.Type.Char => ???
      case IR.Type.String => ???
      case IR.Type.Pointer(_) => vpr.Ref
      case IR.Type.Int => vpr.Int
      case IR.Type.Bool => vpr.Bool
    }
  }

  class GlobalScope(_fields: mutable.Map[String, vpr.Field] = mutable.Map()) {
    lazy val intPtrValue = createField("$int_value", vpr.Int)
    lazy val refPtrValue = createField("$ref_value", vpr.Ref)

    def structField(field: IR.StructField): vpr.Field = createField("$struct_" + field.struct.name + "$" + field.name, getType(this, field.valueType))

    def methodName(originalName: String): String = "$method_" + originalName

    private def createField(name: String, typ: vpr.Type): vpr.Field = {
      _fields.get(name) match {
        case None => {
          val field = vpr.Field(name, typ)()
          _fields += (name -> field)
          field
        }

        case Some(field) => field
      }
    }

    def fields: Seq[vpr.Field] = _fields.values.toSeq.sortBy(_.name)

    def local(returnVar: Option[vpr.LocalVarDecl], variables: Map[IR.Var, vpr.LocalVarDecl]) = {
      new LocalScope(_fields, returnVar, variables)
    }
  }

  class LocalScope(
    _fields: mutable.Map[String, vpr.Field],
    val returnVarDecl: Option[vpr.LocalVarDecl],
    variables: Map[IR.Var, vpr.LocalVarDecl]
  ) extends GlobalScope(_fields) {
    def localVar(variable: IR.Var): vpr.LocalVar = variables.get(variable) match {
      case Some(decl) => vpr.LocalVar(decl.name, decl.typ)()
      case None => throw new TransformerException("Variable not found")
    }

    def returnVar: vpr.LocalVar = returnVarDecl match {
      case Some(ret) => vpr.LocalVar(ret.name, ret.typ)()
      case None => throw new TransformerException("No return value for method")
    }
  }
}