package gvc.transformer
import scala.collection.mutable
import viper.silver.{ast => vpr}

object SilverOutput {
  def expression(scope: LocalScope, expr: IR.Expr): vpr.Exp = {
    expr match {
      case v: IR.Var => scope.localVar(v)
      case string: IR.Literal.String => ???
      case int: IR.Literal.Int => vpr.IntLit(BigInt(int.value))()
      case char: IR.Literal.Char => vpr.IntLit(BigInt(char.value))()
      case bool: IR.Literal.Bool => vpr.BoolLit(bool.value)()
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
        vpr.FieldAccess(expression(scope, deref.subject), scope.pointerValue(deref.subject.varType))()
      }

      case negate: IR.Expr.Negation => vpr.Minus(expression(scope, negate.value))()
      case not: IR.Expr.Not => vpr.Not(expression(scope, not.value))()
      case member: IR.Expr.Member => vpr.FieldAccess(scope.localVar(member.subject), scope.structField(member.field))()
      case alloc: IR.Expr.Alloc =>  throw new TransformerException("Invalid alloc encountered as expression")
      case _: IR.Expr.AllocArray => throw new TransformerException("Arrays are not implemented")

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

          case alloc: IR.Expr.Alloc => {
            val fields = alloc.memberType match {
              case value: IR.Type.StructValue => value.definition.fields.map(scope.structField(_))
              case _ => Seq(scope.pointerValue(alloc.valueType.get))
            }

            Seq(vpr.NewStmt(scope.localVar(assign.subject), fields)())
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
        Seq(vpr.FieldAssign(
          vpr.FieldAccess(scope.localVar(assign.subject),
          scope.pointerValue(assign.subject.varType))(),
          expression(scope, assign.value))())
      }

      case whil: IR.Op.While => {
        Seq(vpr.While(expression(scope, whil.condition), Seq(spec(scope, whil.invariant)), block(scope, whil.body))())
      }

      case iff: IR.Op.If => {
        Seq(vpr.If(expression(scope, iff.condition), block(scope, iff.ifTrue), block(scope, iff.ifFalse))())
      }

      case assert: IR.Op.Assert => Seq() // Ignore run-time asserts

      case assert: IR.Op.AssertSpec => Seq(vpr.Assert(spec(scope, assert.spec))())

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
      case char: IR.Literal.Char => vpr.IntLit(BigInt(char.value))()
      case IR.Literal.Null => vpr.NullLit()()
      case field: IR.FieldValue => fieldValue(scope, field)

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

      case logical: IR.Spec.Logical => {
        val left = spec(scope, logical.left)
        val right = spec(scope, logical.right)
        logical.op match {
          case IR.LogicalOp.Or => vpr.Or(left, right)()
          case IR.LogicalOp.And => vpr.And(left, right)()
        }
      }

      case arith: IR.Spec.Arithmetic => {
        val left = spec(scope, arith.left)
        val right = spec(scope, arith.right)
        arith.op match {
          case IR.ArithmeticOp.Add => vpr.Add(left, right)()
          case IR.ArithmeticOp.Subtract => vpr.Sub(left, right)()
          case IR.ArithmeticOp.Multiply => vpr.Mul(left, right)()
          case IR.ArithmeticOp.Divide => vpr.Div(left, right)()
        }
      }

      case conditional: IR.Spec.Conditional => {
        val condition = spec(scope, conditional.condition)
        val left = spec(scope, conditional.ifTrue)
        val right = spec(scope, conditional.ifTrue)
        vpr.CondExp(condition, left, right)()
      }

      case acc: IR.Spec.Accessibility => vpr.FieldAccessPredicate(field(scope, acc.field), vpr.FullPerm()())()

      case imprecise: IR.Spec.Imprecision => vpr.ImpreciseExp(spec(scope, imprecise.spec))()
    }
  }

  def fieldValue(scope: LocalScope, value: IR.FieldValue): vpr.Exp = {
    value match {
      case variable: IR.Var => scope.localVar(variable)
      case ret: IR.Spec.ReturnValue => scope.returnVar
      case member: IR.Spec.Member => vpr.FieldAccess(fieldValue(scope, member.parent), scope.structField(member.field))()
      case deref: IR.Spec.Dereference => vpr.FieldAccess(fieldValue(scope, deref.pointer), scope.pointerValue(deref.pointerType))()
    }
  }

  def field(scope: LocalScope, value: IR.FieldAccess): vpr.FieldAccess = {
    fieldValue(scope, value) match {
      case access: vpr.FieldAccess => access
      case _ => throw new TransformerException("Invalid field access")
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
      case IR.Type.StructReference(_, _) => vpr.Ref
      case IR.Type.Char => vpr.Int
      case IR.Type.String => vpr.Ref
      case IR.Type.Pointer(_) => vpr.Ref
      case IR.Type.Int => vpr.Int
      case IR.Type.Bool => vpr.Bool
    }
  }

  class GlobalScope(_fields: mutable.Map[String, vpr.Field] = mutable.Map()) {
    private lazy val intPtrValue = createField("$int_value", vpr.Int)
    private lazy val refPtrValue = createField("$ref_value", vpr.Ref)
    private lazy val boolPtrValue = createField("$bool_value", vpr.Bool)

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

    def pointerValue(pointerType: IR.Type) = {
      pointerType match {
        case _: IR.Type.StructReference => refPtrValue

        case IR.Type.Pointer(memberType) => memberType match {
          case _: IR.Type.Array => throw new TransformerException("Arrays are not implemented")
          case _: IR.Type.Pointer | _: IR.Type.StructReference => refPtrValue
          case IR.Type.Int => intPtrValue
          case IR.Type.Char => intPtrValue
          case IR.Type.String => refPtrValue
          case IR.Type.Bool => boolPtrValue
        }

        case _ => throw new TransformerException("Invalid pointer type")
      }
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