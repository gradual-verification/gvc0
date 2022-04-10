package gvc.transformer
import scala.collection.mutable
import gvc.analyzer._

class TransformerException(message: String) extends Exception(message)

object IRTransformer {
  def transform(input: ResolvedProgram): IR.Program = {
    var p = new Transformer(input).transform()
    PointerElimination.transform(p)
    p
  }

  private class Transformer(program: ResolvedProgram) {
    val ir = new IR.Program()

    def transform(): IR.Program = {
      for (dep <- program.dependencies)
        defineDependency(dep)
      for (struct <- program.structDefinitions)
        implementStruct(struct)

      for (predicate <- program.predicateDefinitions)
        definePredicate(predicate)
      for (predicate <- program.predicateDefinitions)
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
      structs
        .get(name)
        .getOrElse(throw new TransformerException(s"Undefined struct '$name'"))

    sealed trait StructItem
    sealed trait StructContainer {
      val children: Map[String, StructItem]
      def field(name: String) =
        children
          .get(name)
          .getOrElse(throw new TransformerException(s"Invalid field '$name'"))
    }

    class StructLayout(
        val children: Map[String, StructItem],
        val struct: IR.Struct
    ) extends StructContainer

    class StructEmbedding(val children: Map[String, StructItem])
        extends StructContainer
        with StructItem
    class StructValue(val field: IR.StructField) extends StructItem

    def defineDependency(declaration: ResolvedUseDeclaration): Unit = {
      if (declaration.isLibrary && !ir.dependencies.exists(_.path == declaration.name)) {
        val dep = ir.addDependency(declaration.name, declaration.isLibrary)
        declaration.dependency match {
          case None => throw new TransformerException("Unresolved dependency")
          case Some(libraryDef) => {
            DependencyTransformer.transform(ir, dep, libraryDef)
          }
        }
      }
    }

    def implementStruct(input: ResolvedStructDefinition): Unit = {
      val struct = ir.struct(input.name) match {
        case struct: IR.Struct => struct
        case struct =>
          throw new TransformerException(s"Invalid struct '${struct.name}")
      }

      def resolveField(
          field: ResolvedStructField,
          base: Option[String]
      ): StructItem = {
        val fullName = base match {
          case Some(n) => n + "_" + field.name
          case None    => field.name
        }

        field.valueType match {
          case ResolvedStructType(structName) =>
            new StructEmbedding(
              structDefs
                .get(structName)
                .getOrElse(
                  throw new TransformerException(
                    s"Undefined struct type '$structName'"
                  )
                )
                .fields
                .map(f => f.name -> resolveField(f, Some(fullName)))
                .toMap
            )
          case valueType =>
            new StructValue(struct.addField(fullName, transformType(valueType)))
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
    private def getStructItem(
        member: ResolvedMember
    ): (ResolvedExpression, StructItem) = {
      val (instance, isPointer) = member.parent match {
        case deref: ResolvedDereference if !member.isArrow =>
          (deref.value, true)
        case other => (other, member.isArrow)
      }

      member.field match {
        case None =>
          throw new TransformerException(s"Invalid field '${member.fieldName}'")
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
    private def transformField(
        member: ResolvedMember
    ): (ResolvedExpression, IR.StructField) = {
      val (parent, item) = getStructItem(member)
      item match {
        case _: StructEmbedding =>
          throw new TransformerException("Invalid access of embedded struct")
        case value: StructValue => (parent, value.field)
      }
    }

    def transformReturnType(t: ResolvedType): Option[IR.Type] =
      t match {
        case VoidType => None
        case t        => Some(transformType(t))
      }

    def transformType(t: ResolvedType): IR.Type =
      t match {
        case UnknownType => throw new TransformerException("Unknown type")
        case MissingNamedType(name) =>
          throw new TransformerException(s"Missing type '$name'")
        case ResolvedStructType(structName) =>
          throw new TransformerException(
            s"Invalid bare struct value '$structName'"
          )
        case ResolvedPointer(struct: ResolvedStructType) =>
          new IR.ReferenceType(ir.struct(struct.structName))
        case ResolvedPointer(valueType) =>
          new IR.PointerType(transformType(valueType))
        case ResolvedArray(valueType) =>
          throw new TransformerException("Unsupported array type")
        case BoolType => IR.BoolType
        case IntType  => IR.IntType
        case CharType => IR.CharType
        case StringType =>
          throw new TransformerException("Unsupported string type")
        case NullType => throw new TransformerException("Invalid NULL type")
        case VoidType => throw new TransformerException("Invalid void type")
      }

    def defineMethod(input: ResolvedMethodDefinition): Unit = {
      val method = ir.addMethod(
        input.name,
        transformReturnType(input.declaration.returnType)
      )
      for (param <- input.declaration.arguments) {
        method.addParameter(transformType(param.valueType), param.name)
      }
    }

    sealed trait Scope {
      def variable(name: String): IR.Var

      def variable(input: ResolvedVariableRef): IR.Var = {
        input.variable match {
          case None =>
            throw new TransformerException("Invalid variable reference")
          case Some(v) => variable(v.name)
        }
      }

      def +=(op: IR.Op): Unit =
        throw new TransformerException(
          "Invalid imperative statement encountered"
        )
    }

    sealed trait MethodScope extends Scope {
      def method: IR.Method
      def vars: Map[String, IR.Var]

      def variable(name: String): IR.Var = {
        vars.getOrElse(
          name,
          throw new TransformerException(s"Variable '$name' not found")
        )
      }
    }

    class BlockScope(
        val method: IR.Method,
        val output: IR.Block,
        val vars: Map[String, IR.Var]
    ) extends MethodScope {
      override def +=(op: IR.Op): Unit =
        output += op
    }

    class ConditionalScope(
        val parent: MethodScope,
        val conditions: List[IR.Expression]
    ) extends MethodScope {
      def method = parent.method
      def vars = parent.vars

      lazy val conditionalBlock = {
        val cond = conditions.reduceLeft((x, y) =>
          new IR.Binary(IR.BinaryOp.And, x, y)
        )
        val ifOp = new IR.If(cond)
        parent += ifOp
        ifOp.ifTrue
      }

      override def +=(op: IR.Op): Unit =
        conditionalBlock += op
    }

    class CollectorScope(
        parent: MethodScope
    ) extends MethodScope {
      def method = parent.method
      def vars = parent.vars

      val ops = mutable.ListBuffer[IR.Op]()
      override def +=(op: IR.Op): Unit =
        ops += op
    }

    def implementMethod(input: ResolvedMethodDefinition): Unit = {
      val method = ir.method(input.name) match {
        case method: IR.Method => method
        case method =>
          throw new TransformerException(s"Invalid method '${method.name}'")
      }

      val scope = new BlockScope(
        method,
        method.body,
        method.parameters.map(p => p.name -> p).toMap
      )
      method.precondition =
        input.declaration.precondition.map(transformSpec(_, scope))
      transformStatement(input.body, scope)
      method.postcondition =
        input.declaration.postcondition.map(transformSpec(_, scope))

      ReassignmentElimination.transform(method)
      ParameterAssignmentElimination.transform(method)
    }

    def transformStatement(
        input: ResolvedStatement,
        scope: MethodScope
    ): Unit = {
      input match {
        case block: ResolvedBlock => {
          val vars = block.variableDefs
            .map(v =>
              v.name -> scope.method.addVar(transformType(v.valueType), v.name)
            )

          val child = scope match {
            case scope: BlockScope =>
              new BlockScope(scope.method, scope.output, scope.vars ++ vars)
            case _ => throw new TransformerException("Invalid block")
          }

          block.statements.foreach(transformStatement(_, child))
        }

        case iff: ResolvedIf => {
          val ir = new IR.If(transformExpr(iff.condition, scope))
          scope += ir

          transformStatement(
            iff.ifTrue,
            new BlockScope(scope.method, ir.ifTrue, scope.vars)
          )
          iff.ifFalse.foreach(
            transformStatement(
              _,
              new BlockScope(scope.method, ir.ifFalse, scope.vars)
            )
          )
        }

        case loop: ResolvedWhile => {
          val condScope = new CollectorScope(scope)
          val cond = transformExpr(loop.condition, condScope)
          condScope.ops.foreach(scope += _)

          val ir =
            new IR.While(cond, loop.invariant.map(transformSpec(_, scope)).getOrElse(new IR.Imprecise(None)))
          scope += ir

          val bodyScope = new BlockScope(scope.method, ir.body, scope.vars)
          transformStatement(loop.body, bodyScope)
          condScope.ops.foreach(ir.body += _.copy)
        }

        case expr: ResolvedExpressionStatement =>
          expr.value match {
            case invoke: ResolvedInvoke => invokeVoid(invoke, scope)
            case expr =>
              transformExpr(
                expr,
                scope
              ) // traverse expression and ignore result
          }

        case assign: ResolvedAssignment =>
          assign.value match {
            case invoke: ResolvedInvoke =>
              assign.left match {
                case ref: ResolvedVariableRef if assign.operation == None =>
                  // Avoid introducing a temp var for the case when the result
                  // is immediately assigned to a var
                  invokeToVar(invoke, scope.variable(ref), scope)
                case complex =>
                  scope += transformAssign(
                    complex,
                    transformExpr(invoke, scope),
                    assign.operation,
                    scope
                  )
              }

            case alloc: ResolvedAlloc => {
              val valueType = transformType(alloc.valueType)
              assign.left match {
                // Avoid introducing a temp var for the case when the result
                // is immediately assigned to a var
                case ref: ResolvedVariableRef if assign.operation == None =>
                  scope += transformAlloc(alloc, scope.variable(ref), scope)
                case complex =>
                  scope += transformAssign(
                    complex,
                    transformExpr(alloc, scope),
                    assign.operation,
                    scope
                  )
              }
            }
            case expr =>
              scope += transformAssign(
                assign.left,
                transformExpr(expr, scope),
                assign.operation,
                scope
              )
          }

        case inc: ResolvedIncrement => {
          // In C0, L-values cannot contain methods, which means that the L-value
          // of increment is free of side-effects and can be evaluated multiple times

          val current = transformExpr(inc.value, scope)
          val op = inc.operation match {
            case IncrementOperation.Increment => IR.BinaryOp.Add
            case IncrementOperation.Decrement => IR.BinaryOp.Subtract
          }

          val computed = new IR.Binary(op, current, new IR.IntLit(1))
          scope += transformAssign(inc.value, computed, None, scope)
        }

        case ret: ResolvedReturn =>
          scope += new IR.Return(ret.value.map(transformExpr(_, scope)))

        case assert: ResolvedAssert =>
          scope += new IR.Assert(
            transformExpr(assert.value, scope),
            IR.AssertKind.Imperative
          )

        case spec: ResolvedAssertSpecification =>
          scope += new IR.Assert(
            transformSpec(spec.specification, scope),
            IR.AssertKind.Specification
          )

        case unfold: ResolvedUnfoldPredicate =>
          scope += new IR.Unfold(
            transformPredicate(unfold.predicate, scope)
          )

        case fold: ResolvedFoldPredicate =>
          scope += new IR.Fold(transformPredicate(fold.predicate, scope))

        case err: ResolvedError =>
          scope += new IR.Error(transformExpr(err.value, scope))
      }
    }

    def definePredicate(input: ResolvedPredicateDefinition): Unit = {
      val pred = ir.addPredicate(input.name)
      for (param <- input.declaration.arguments)
        pred.addParameter(transformType(param.valueType), param.name)
    }

    class PredicateScope(val predicate: IR.Predicate) extends Scope {
      private val params = predicate.parameters.map(p => p.name -> p).toMap

      def variable(name: String): IR.Var =
        params
          .get(name)
          .getOrElse(
            throw new TransformerException(
              s"Predicate parameter '$name' not found"
            )
          )

      // Cannot add operations, so conditional scope is a no-op
      def conditional(cond: IR.Expression) = this
    }

    def implementPredicate(input: ResolvedPredicateDefinition): Unit = {
      val predicate = ir.predicate(input.name)
      val scope = new PredicateScope(predicate)
      predicate.expression = transformSpec(input.body, scope)
    }

    def not(condition: IR.Expression) =
      new IR.Unary(IR.UnaryOp.Not, condition)

    def conditionalScope(scope: Scope, condition: IR.Expression) =
      scope match {
        case scope: PredicateScope => scope
        case scope: ConditionalScope =>
          new ConditionalScope(scope.parent, scope.conditions :+ condition)
        case scope: MethodScope => new ConditionalScope(scope, List(condition))
      }

    def transformExpr(
        input: ResolvedExpression,
        scope: Scope
    ): IR.Expression = input match {
      case ref: ResolvedVariableRef => scope.variable(ref)
      case pred: ResolvedPredicate  => transformPredicate(pred, scope)
      case invoke: ResolvedInvoke   => invokeToValue(invoke, scope)
      case alloc: ResolvedAlloc     => allocToValue(alloc, scope)

      case m: ResolvedMember => {
        val (parent, field) = transformField(m)
        new IR.FieldMember(transformExpr(parent, scope), field)
      }

      case _: ResolvedArrayIndex | _: ResolvedLength | _: ResolvedAllocArray =>
        throw new TransformerException("Arrays are not supported")

      case _: ResolvedResult =>
        scope match {
          case scope: MethodScope => new IR.Result(scope.method)
          case _ =>
            throw new TransformerException("Result used in invalid context")
        }

      case acc: ResolvedAccessibility =>
        new IR.Accessibility(transformExpr(acc.field, scope) match {
          case member: IR.Member => member
          case _                      => throw new TransformerException("Invalid acc() argument")
        })

      case imp: ResolvedImprecision =>
        new IR.Imprecise(None)

      case cond: ResolvedTernary => {
        val condition = transformExpr(cond.condition, scope)
        val ifTrue =
          transformExpr(cond.ifTrue, conditionalScope(scope, condition))
        val ifFalse =
          transformExpr(cond.ifFalse, conditionalScope(scope, not(condition)))
        new IR.Conditional(condition, ifTrue, ifFalse)
      }

      case arith: ResolvedArithmetic => {
        val op = arith.operation match {
          case ArithmeticOperation.Add      => IR.BinaryOp.Add
          case ArithmeticOperation.Subtract => IR.BinaryOp.Subtract
          case ArithmeticOperation.Multiply => IR.BinaryOp.Multiply
          case ArithmeticOperation.Divide   => IR.BinaryOp.Divide
        }

        new IR.Binary(
          op,
          transformExpr(arith.left, scope),
          transformExpr(arith.right, scope)
        )
      }

      case comp: ResolvedComparison => {
        val op = comp.operation match {
          case ComparisonOperation.EqualTo    => IR.BinaryOp.Equal
          case ComparisonOperation.NotEqualTo => IR.BinaryOp.NotEqual
          case ComparisonOperation.LessThan   => IR.BinaryOp.Less
          case ComparisonOperation.LessThanOrEqualTo =>
            IR.BinaryOp.LessOrEqual
          case ComparisonOperation.GreaterThan => IR.BinaryOp.Greater
          case ComparisonOperation.GreaterThanOrEqualTo =>
            IR.BinaryOp.GreaterOrEqual
        }

        new IR.Binary(
          op,
          transformExpr(comp.left, scope),
          transformExpr(comp.right, scope)
        )
      }

      case logic: ResolvedLogical => {
        val left = transformExpr(logic.left, scope)
        val (op, rightCond) = logic.operation match {
          case LogicalOperation.And => (IR.BinaryOp.And, left)
          case LogicalOperation.Or  => (IR.BinaryOp.Or, not(left))
        }
        val right =
          transformExpr(logic.right, conditionalScope(scope, rightCond))
        new IR.Binary(op, left, right)
      }

      case deref: ResolvedDereference => {
        new IR.DereferenceMember(transformExpr(deref.value, scope))
      }

      case not: ResolvedNot =>
        new IR.Unary(IR.UnaryOp.Not, transformExpr(not.value, scope))
      case negate: ResolvedNegation =>
        new IR.Unary(
          IR.UnaryOp.Negate,
          transformExpr(negate.value, scope)
        )
      case _: ResolvedString =>
        throw new TransformerException("Strings are not supported")
      case char: ResolvedChar => new IR.CharLit(char.value)
      case int: ResolvedInt   => new IR.IntLit(int.value)
      case b: ResolvedBool    => new IR.BoolLit(b.value)
      case _: ResolvedNull    => new IR.NullLit()
    }

    // Catches a ? specifier and wraps it in an Imprecise object
    def transformSpec(
        input: ResolvedExpression,
        scope: Scope
    ): IR.Expression = input match {
      case _: ResolvedImprecision => new IR.Imprecise(None)

      case logical: ResolvedLogical => {
        val (left, leftImp) = transformSpec(logical.left, scope) match {
          case imp: IR.Imprecise => (imp.precise, true)
          case other                  => (Some(other), false)
        }

        val (right, rightImp) = transformSpec(logical.right, scope) match {
          case imp: IR.Imprecise => (imp.precise, true)
          case other                  => (Some(other), false)
        }

        if ((leftImp || rightImp) && logical.operation != LogicalOperation.And)
          throw new TransformerException("Invalid ? expression")

        (left, right) match {
          case (None, None)      => new IR.Imprecise(None)
          case (None, Some(exp)) => new IR.Imprecise(Some(exp))
          case (Some(exp), None) => new IR.Imprecise(Some(exp))
          case (Some(l), Some(r)) => {
            val op = logical.operation match {
              case LogicalOperation.And => IR.BinaryOp.And
              case LogicalOperation.Or  => IR.BinaryOp.Or
            }
            val exp = new IR.Binary(op, l, r)
            if (leftImp || rightImp) new IR.Imprecise(Some(exp))
            else exp
          }
        }
      }

      case other => transformExpr(input, scope)
    }

    def allocToValue(input: ResolvedAlloc, scope: Scope): IR.Var =
      scope match {
        case scope: MethodScope => {
          val valueType = transformType(input.valueType)
          val temp = scope.method.addVar(valueType)
          scope += transformAlloc(input, temp, scope)
          temp
        }

        case _ => throw new TransformerException("Invalid alloc")
      }

    def invokeToValue(input: ResolvedInvoke, scope: Scope): IR.Var = {
      scope match {
        case scope: MethodScope => {
          val callee = resolveMethod(input)
          val retType = callee.returnType.getOrElse(
            throw new TransformerException("Cannot use result of void method")
          )
          val args = input.arguments.map(transformExpr(_, scope))
          val temp = scope.method.addVar(retType)
          scope += new IR.Invoke(callee, args, Some(temp))
          temp
        }

        case _ =>
          throw new TransformerException(
            s"Invalid invoke: '${input.methodName}'"
          )
      }
    }

    def invokeToVar(
        input: ResolvedInvoke,
        target: IR.Var,
        scope: MethodScope
    ): Unit = {
      val method = resolveMethod(input)
      val args = input.arguments.map(transformExpr(_, scope))
      scope += new IR.Invoke(method, args, Some(target))
    }

    def invokeVoid(input: ResolvedInvoke, scope: Scope): Unit = {
      val method = resolveMethod(input)
      val args = input.arguments.map(transformExpr(_, scope))
      scope += new IR.Invoke(method, args, None)
    }

    def resolveMethod(invoke: ResolvedInvoke): IR.MethodDefinition =
      invoke.method
        .map(m => ir.method(m.name))
        .getOrElse(throw new TransformerException("Invalid invoke"))

    def resolvePredicate(pred: ResolvedPredicate): IR.Predicate =
      pred.predicate
        .map(p => ir.predicate(p.name))
        .getOrElse(
          throw new TransformerException("Invalid predicate reference")
        )

    def transformPredicate(
        pred: ResolvedPredicate,
        scope: Scope
    ): IR.PredicateInstance =
      new IR.PredicateInstance(
        resolvePredicate(pred),
        pred.arguments.map(transformExpr(_, scope))
      )

    def transformAssign(
        target: ResolvedExpression,
        value: IR.Expression,
        op: Option[ArithmeticOperation],
        scope: Scope
    ): IR.Op = {
      target match {
        case ref: ResolvedVariableRef => {
          val target = scope.variable(ref)
          new IR.Assign(target, transformAssignValue(value, target, op))
        }

        case member: ResolvedMember => {
          val (parent, field) = transformField(member)
          val target =
            new IR.FieldMember(transformExpr(parent, scope), field)
          new IR.AssignMember(
            target,
            transformAssignValue(value, target, op)
          )
        }

        case deref: ResolvedDereference =>
          val target =
            new IR.DereferenceMember(transformExpr(deref.value, scope))
          new IR.AssignMember(
            target,
            transformAssignValue(value, target, op)
          )

        case _: ResolvedArrayIndex =>
          throw new TransformerException("Arrays are not supported")
        case _ => throw new TransformerException("Invalid L-value")
      }
    }

    def transformAssignValue(
        value: IR.Expression,
        target: IR.Expression,
        op: Option[ArithmeticOperation]
    ): IR.Expression = {
      op match {
        case None => value
        case Some(op) => {
          val binOp = op match {
            case ArithmeticOperation.Add      => IR.BinaryOp.Add
            case ArithmeticOperation.Subtract => IR.BinaryOp.Subtract
            case ArithmeticOperation.Divide   => IR.BinaryOp.Divide
            case ArithmeticOperation.Multiply => IR.BinaryOp.Multiply
          }
          new IR.Binary(binOp, target, value)
        }
      }
    }

    def transformAlloc(
        input: ResolvedAlloc,
        target: IR.Var,
        scope: Scope
    ): IR.Op =
      input.memberType match {
        case ResolvedStructType(structName) =>
          new IR.AllocStruct(ir.struct(structName), target)
        case valueType =>
          new IR.AllocValue(transformType(valueType), target)
      }
  }
}
