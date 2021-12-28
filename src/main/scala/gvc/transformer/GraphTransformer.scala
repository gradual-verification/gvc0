package gvc.transformer
import scala.collection.mutable
import gvc.analyzer._

object GraphTransformer {
  class TransformerException(message: String) extends Exception(message)

  def transform(input: ResolvedProgram): IRGraph.Program = {
    new Transformer(input).transform()
  }

  private class Transformer(program: ResolvedProgram) {
    val ir = new IRGraph.Program()

    def transform(): IRGraph.Program = {
      for (struct <- program.structDefinitions)
        implementStruct(struct)

      for (predicate <- program.predicateDefinitions)
        definePredicate(predicate)
      for(predicate <- program.predicateDefinitions)
        implementPredicate(predicate)

      for (method <- program.methodDefinitions)
        defineMethod(method)
      for (method <- program.methodDefinitions)
        implementMethod(method)

      ir
    }

    // Data for struct flattening (i.e. embedding a value-type struct
    // within another struct by copying the list of fields)
    private val structs = mutable.Map[String, StructLayout]()
    private val structDefs = program.structDefinitions
      .map(s => s.name -> s)
      .toMap

    def getStructLayout(name: String) =
      structs.get(name).getOrElse(throw new TransformerException(s"Undefined struct '$name'"))

    sealed trait StructItem
    sealed trait StructContainer {
      val children: Map[String, StructItem]
      def field(name: String) =
        children.get(name)
          .getOrElse(throw new TransformerException(s"Invalid field '$name'"))
    }

    class StructLayout(
      val children: Map[String, StructItem],
      val struct: IRGraph.Struct) extends StructContainer

    class StructEmbedding(val children: Map[String, StructItem]) extends StructContainer with StructItem
    class StructValue(val field: IRGraph.StructField) extends StructItem

    def implementStruct(input: ResolvedStructDefinition): Unit = {
      val struct = ir.struct(input.name)

      def resolveField(field: ResolvedStructField, base: Option[String]): StructItem = {
        val fullName = base match {
          case Some(n) => n + "_" + field.name
          case None => field.name
        }

        field.valueType match {
          case ResolvedStructType(structName) =>
            new StructEmbedding(structDefs.get(structName)
              .getOrElse(throw new TransformerException(s"Undefined struct type '$structName'"))
              .fields.map(f => f.name -> resolveField(f, Some(fullName))).toMap)
          case valueType => new StructValue(struct.addField(fullName, transformType(valueType)))
        }
      }

      structs += input.name -> new StructLayout(
        input.fields.map(f => f.name -> resolveField(f, None)).toMap,
        struct
      )
    }

    // Looks up the field flattening information and returns the struct item specified,
    // skipping any flattened fields.
    // Returns the struct item and the expression for the concrete struct (the field's parent).
    private def getStructItem(member: ResolvedMember): (ResolvedExpression, StructItem) = {
      val (instance, isPointer) = member.parent match {
        case deref: ResolvedDereference if !member.isArrow => (deref.value, true)
        case other => (other, member.isArrow)
      }

      member.field match {
        case None => throw new TransformerException(s"Invalid field '${member.fieldName}'")
        case Some(field) => {
          instance match {
            // Embedded structs must be accessed by a dot, not an arrow
            case instance: ResolvedMember if !isPointer => {
              val (root, node) = getStructItem(instance)
              node match {
                case embed: StructEmbedding => (root, embed.field(field.name))
                // Dotted member, but there is no corresponding embedded field
                case _ => throw new TransformerException("Invalid dotted field")
              }
            }

            case instance => {
              (instance, getStructLayout(field.structName).field(field.name))
            }
          }
        }
      }
    }

    // Looks up the correct field (including skipping flattened member expressions), and returns
    // the parent expression and the IR field.
    private def transformField(member: ResolvedMember): (ResolvedExpression, IRGraph.StructField) = {
      val (parent, item) = getStructItem(member)
      item match {
        case _: StructEmbedding => throw new TransformerException("Invalid access of embedded struct")
        case value: StructValue => (parent, value.field)
      }
    }

    def transformReturnType(t: ResolvedType): Option[IRGraph.Type] =
      t match {
        case VoidType => None
        case t => Some(transformType(t))
      }

    def transformType(t: ResolvedType): IRGraph.Type =
      t match {
        case UnknownType => throw new TransformerException("Unknown type")
        case MissingNamedType(name) => throw new TransformerException(s"Missing type '$name'")
        case ResolvedStructType(structName) => throw new TransformerException(s"Invalid bare struct value '$structName'")
        case ResolvedPointer(struct: ResolvedStructType) => new IRGraph.ReferenceType(ir.struct(struct.structName))
        case ResolvedPointer(valueType) => new IRGraph.PointerType(transformType(valueType))
        case ResolvedArray(valueType) => throw new TransformerException("Unsupported array type")
        case BoolType => IRGraph.BoolType
        case IntType => IRGraph.IntType
        case CharType => IRGraph.CharType
        case StringType => throw new TransformerException("Unsupported string type")
        case NullType => throw new TransformerException("Invalid NULL type")
        case VoidType => throw new TransformerException("Invalid void type")
      }

    def defineMethod(input: ResolvedMethodDefinition): Unit = {
      val method = ir.addMethod(input.name, transformReturnType(input.declaration.returnType))
      for (param <- input.declaration.arguments) {
        method.addParameter(transformType(param.valueType), param.name)
      }
    }

    sealed trait Scope {
      def variable(name: String): IRGraph.Var

      def variable(input: ResolvedVariableRef): IRGraph.Var = {
        input.variable match {
          case None => throw new TransformerException("Invalid variable reference")
          case Some(v) => variable(v.name)
        }
      }
    }

    class MethodScope(
      val method: IRGraph.Method,
      initialVars: Seq[(String, IRGraph.Var)],
      val parent: Option[Scope]
    ) extends Scope {
      private val vars = mutable.Map[String,IRGraph.Var](initialVars:_*)

      def variable(name: String): IRGraph.Var = {
        vars.get(name)
          .orElse(parent.map(_.variable(name)))
          .getOrElse(throw new TransformerException(s"Variable '$name' not found"))
      }

      def declareVariable(valueType: IRGraph.Type, name: String): IRGraph.Var = {
        val newVar = method.addVar(valueType, name)
        vars += (name -> newVar)
        newVar
      }

      def child() = new MethodScope(method, Seq.empty, Some(this))
    }

    def implementMethod(input: ResolvedMethodDefinition): Unit = {
      val method = ir.method(input.name)
      val scope = new MethodScope(method, method.parameters.map(p => p.name -> p), None)
      method.precondition = input.declaration.precondition.map(transformSpec(_, scope))
      transformBlock(input.body, method.body, scope)
      method.postcondition = input.declaration.postcondition.map(transformSpec(_, scope))
    }

    def transformBlock(
      input: ResolvedBlock,
      output: IRGraph.Block,
      scope: MethodScope): Unit = {
      val blockScope = scope.child()
      for (decl <- input.variableDefs) {
        blockScope.declareVariable(transformType(decl.valueType), decl.name)
      }

      for (stmt <- input.statements) {
        transformStatement(stmt, output, blockScope)
      }
    }

    def transformStatement(input: ResolvedStatement, output: IRGraph.Block, scope: MethodScope): Unit = {
      input match {
        case block: ResolvedBlock => transformBlock(block, output, scope)

        case iff: ResolvedIf => {
          val ir = new IRGraph.If(invokeExpr(iff.condition, output, scope))
          transformStatement(iff.ifTrue, ir.ifTrue, scope)
          iff.ifFalse.foreach(transformStatement(_, ir.ifFalse, scope))
          output += ir
        }

        case loop: ResolvedWhile => {
          val ir = new IRGraph.While(
            transformExpr(loop.condition, scope),
            loop.invariant.map(transformSpec(_, scope)))
          transformStatement(loop.body, ir.body, scope)
          output += ir
        }

        case expr: ResolvedExpressionStatement => expr.value match {
          case invoke: ResolvedInvoke => invokeVoid(invoke, output, scope)
          case expr => transformExpr(expr, scope) // traverse expression to make sure it is valid
        }

        case assign: ResolvedAssignment => assign.value match {
          case invoke: ResolvedInvoke => assign.left match {
            case ref: ResolvedVariableRef =>
              invokeToVar(invoke, scope.variable(ref), output, scope)
            case complex =>
              output += transformAssign(complex, invokeToValue(invoke, output, scope), scope)
          }

          case alloc: ResolvedAlloc => {
            val valueType = transformType(alloc.valueType)
            // Create a temporary variable if assigning to complex expression
            assign.left match {
              case ref: ResolvedVariableRef => output += transformAlloc(alloc, scope.variable(ref), scope)
              case complex => {
                val target = scope.method.addVar(valueType)
                output += transformAlloc(alloc, target, scope)
                output += transformAssign(complex, target, scope)
              }
            }
          }

          case expr => output += transformAssign(assign.left, transformExpr(expr, scope), scope)
        }

        case inc: ResolvedIncrement => {
          // In C0, L-values cannot contain methods, which means that the L-value
          // of increment is free of side-effects and can be evaluated multiple times

          val current = transformExpr(inc.value, scope)
          val op = inc.operation match {
            case IncrementOperation.Increment => IRGraph.BinaryOp.Add
            case IncrementOperation.Decrement => IRGraph.BinaryOp.Subtract
          }

          val computed = new IRGraph.Binary(op, current, new IRGraph.Int(1))
          output += transformAssign(inc.value, computed, scope)
        }

        case ret: ResolvedReturn =>
          output += new IRGraph.Return(ret.value.map(invokeExpr(_, output, scope)))

        case assert: ResolvedAssert =>
          output += new IRGraph.Assert(invokeExpr(assert.value, output, scope), IRGraph.AssertKind.Imperative)
        
        case spec: ResolvedAssertSpecification =>
          output += new IRGraph.Assert(transformSpec(spec.specification, scope), IRGraph.AssertKind.Specification)

        case unfold: ResolvedUnfoldPredicate =>
          output += new IRGraph.Unfold(transformPredicate(unfold.predicate, scope))

        case fold: ResolvedFoldPredicate =>
          output += new IRGraph.Fold(transformPredicate(fold.predicate, scope))

        case err: ResolvedError =>
          output += new IRGraph.Error(invokeExpr(err.value, output, scope))
      }
    }

    def definePredicate(input: ResolvedPredicateDefinition): Unit = {
      val pred = ir.addPredicate(input.name)
      for (param <- input.declaration.arguments)
        pred.addParameter(transformType(param.valueType), param.name)
    }

    class PredicateScope(val predicate: IRGraph.Predicate) extends Scope {
      private val params = predicate.parameters.map(p => p.name -> p).toMap

      def variable(name: String): IRGraph.Var =
        params.get(name).getOrElse(throw new TransformerException(s"Predicate parameter '$name' not found"))
    }

    def implementPredicate(input: ResolvedPredicateDefinition): Unit = {
      val predicate = ir.predicate(input.name)
      val scope = new PredicateScope(predicate)
      predicate.expression = transformExpr(input.body, scope)
    }

    def transformExpr(input: ResolvedExpression, scope: Scope): IRGraph.Expression = input match {
      case ref: ResolvedVariableRef => scope.variable(ref)
      case pred: ResolvedPredicate => transformPredicate(pred, scope)
      case _: ResolvedInvoke => throw new TransformerException("Using invoke in a complex expression is not supported")

      case m: ResolvedMember => {
        val (parent, field) = transformField(m)
        new IRGraph.FieldMember(transformExpr(parent, scope), field)
      }

      case _: ResolvedArrayIndex | _: ResolvedLength | _: ResolvedAllocArray =>
        throw new TransformerException("Arrays are not supported")

      case _: ResolvedResult => scope match {
        case scope: MethodScope => new IRGraph.Result(scope.method)
        case _ => throw new TransformerException("Result used in invalid context")
      }

      case acc: ResolvedAccessibility =>
        new IRGraph.Accessibility(transformExpr(acc.field, scope) match {
          case member: IRGraph.Member => member
          case _ => throw new TransformerException("Invalid acc() argument")
        })

      case imp: ResolvedImprecision => throw new TransformerException("Invalid ? encountered as expression")
      
      case cond: ResolvedTernary =>
        new IRGraph.Conditional(
          transformExpr(cond.condition, scope),
          transformExpr(cond.ifTrue, scope),
          transformExpr(cond.ifFalse, scope))

      case arith: ResolvedArithmetic => {
        val op = arith.operation match {
          case ArithmeticOperation.Add => IRGraph.BinaryOp.Add
          case ArithmeticOperation.Subtract => IRGraph.BinaryOp.Subtract
          case ArithmeticOperation.Multiply => IRGraph.BinaryOp.Multiply
          case ArithmeticOperation.Divide => IRGraph.BinaryOp.Divide
        }

        new IRGraph.Binary(op, transformExpr(arith.left, scope), transformExpr(arith.right, scope))
      }

      case comp: ResolvedComparison => {
        val op = comp.operation match {
          case ComparisonOperation.EqualTo => IRGraph.BinaryOp.Equal
          case ComparisonOperation.NotEqualTo => IRGraph.BinaryOp.NotEqual
          case ComparisonOperation.LessThan => IRGraph.BinaryOp.Less
          case ComparisonOperation.LessThanOrEqualTo => IRGraph.BinaryOp.LessOrEqual
          case ComparisonOperation.GreaterThan => IRGraph.BinaryOp.Greater
          case ComparisonOperation.GreaterThanOrEqualTo => IRGraph.BinaryOp.GreaterOrEqual
        }

        new IRGraph.Binary(op, transformExpr(comp.left, scope), transformExpr(comp.right, scope))
      }

      case logic: ResolvedLogical => {
        val op = logic.operation match {
          case LogicalOperation.And => IRGraph.BinaryOp.And
          case LogicalOperation.Or => IRGraph.BinaryOp.Or
        }
        new IRGraph.Binary(op, transformExpr(logic.left, scope), transformExpr(logic.right, scope))
      }

      case deref: ResolvedDereference => {
        new IRGraph.DereferenceMember(transformExpr(deref.value, scope), transformType(deref.valueType))
      }

      case not: ResolvedNot => new IRGraph.Unary(IRGraph.UnaryOp.Not, transformExpr(not.value, scope))
      case negate: ResolvedNegation => new IRGraph.Unary(IRGraph.UnaryOp.Negate, transformExpr(negate.value, scope))
      case _: ResolvedAlloc => throw new TransformerException("Using alloc in a complex expression is not supported")
      case _: ResolvedString => throw new TransformerException("Strings are not supported")
      case char: ResolvedChar => new IRGraph.Char(char.value)
      case int: ResolvedInt => new IRGraph.Int(int.value)
      case b: ResolvedBool => new IRGraph.Bool(b.value)
      case _: ResolvedNull => new IRGraph.Null()
    }

    // Catches a ? specifier and wraps it in an Imprecise object
    def transformSpec(input: ResolvedExpression, scope: Scope): IRGraph.Expression = input match {
      case _: ResolvedImprecision => new IRGraph.Imprecise(None)

      case logical: ResolvedLogical => {
        val (left, leftImp) = transformSpec(logical.left, scope) match {
          case imp: IRGraph.Imprecise => (imp.precise, true)
          case other => (Some(other), false)
        }

        val (right, rightImp) = transformSpec(logical.right, scope) match {
          case imp: IRGraph.Imprecise => (imp.precise, true)
          case other => (Some(other), false)
        }

        if ((leftImp || rightImp) && logical.operation != LogicalOperation.And)
          throw new TransformerException("Invalid ? expression")
        
        (left, right) match {
          case (None, None) => new IRGraph.Imprecise(None)
          case (None, Some(exp)) => new IRGraph.Imprecise(Some(exp))
          case (Some(exp), None) => new IRGraph.Imprecise(Some(exp))
          case (Some(l), Some(r)) => {
            val op = logical.operation match {
              case LogicalOperation.And => IRGraph.BinaryOp.And
              case LogicalOperation.Or => IRGraph.BinaryOp.Or
            }
            val exp = new IRGraph.Binary(op, l, r)
            if (leftImp || rightImp) new IRGraph.Imprecise(Some(exp))
            else exp
          }
        }
      }

      case other => transformExpr(input, scope)
    }

    def invokeExpr(input: ResolvedExpression, output: IRGraph.Block, scope: MethodScope): IRGraph.Expression = {
      input match {
        case invoke: ResolvedInvoke => invokeToValue(invoke, output, scope)
        case _ => transformExpr(input, scope)
      }
    }

    def invokeToValue(input: ResolvedInvoke, output: IRGraph.Block, scope: MethodScope): IRGraph.Var = {
      val method = resolveMethod(input)
      val retType = method.returnType.getOrElse(throw new TransformerException("Cannot use result of void method"))
      val args = input.arguments.map(transformExpr(_, scope))
      val temp = scope.method.addVar(retType)
      output += new IRGraph.Invoke(method, args, Some(temp))
      temp
    }

    def invokeToVar(input: ResolvedInvoke, target: IRGraph.Var, output: IRGraph.Block, scope: MethodScope): Unit = {
      val method = resolveMethod(input)
      val args = input.arguments.map(transformExpr(_, scope))
      output += new IRGraph.Invoke(method, args, Some(target))
    }

    def invokeVoid(input: ResolvedInvoke, output: IRGraph.Block, scope: Scope): Unit = {
      val method = resolveMethod(input)
      val args = input.arguments.map(transformExpr(_, scope))
      output += new IRGraph.Invoke(method, args, None)
    }

    def resolveMethod(invoke: ResolvedInvoke): IRGraph.Method =
      invoke.method.map(m => ir.method(m.name))
        .getOrElse(throw new TransformerException("Invalid invoke"))

    def resolvePredicate(pred: ResolvedPredicate): IRGraph.Predicate =
      pred.predicate.map(p => ir.predicate(p.name))
        .getOrElse(throw new TransformerException("Invalid predicate reference"))

    def transformPredicate(pred: ResolvedPredicate, scope: Scope): IRGraph.PredicateInstance =
      new IRGraph.PredicateInstance(resolvePredicate(pred), pred.arguments.map(transformExpr(_, scope)))

    def transformAssign(target: ResolvedExpression, value: IRGraph.Expression, scope: Scope): IRGraph.Op = {
      target match {
        case ref: ResolvedVariableRef => new IRGraph.Assign(scope.variable(ref), value)

        case member: ResolvedMember => {
          val (parent, field) = transformField(member)
          new IRGraph.AssignMember(new IRGraph.FieldMember(transformExpr(parent, scope), field), value)
        }

        case deref: ResolvedDereference =>
          new IRGraph.AssignMember(new IRGraph.DereferenceMember(transformExpr(deref.value, scope), transformType(deref.valueType)), value)

        case _: ResolvedArrayIndex => throw new TransformerException("Arrays are not supported")
        case _ => throw new TransformerException("Invalid L-value")
      }
    }

    def transformAlloc(input: ResolvedAlloc, target: IRGraph.Var, scope: Scope): IRGraph.Op =
      input.memberType match {
        case ResolvedStructType(structName) => new IRGraph.AllocStruct(ir.struct(structName), target)
        case valueType => new IRGraph.AllocValue(transformType(valueType), target)
      }
  }
}