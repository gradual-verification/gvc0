package gvc.transformer

import gvc.analyzer._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable

class TransformerException(val message: String) extends RuntimeException {
  override def getMessage(): String = message
}

object Transformer {

  // Struct flattening data structures
  class StructTree(val children: List[StructNode], val struct: StructDefImpl) {
    def fields = children.flatMap(_.fields)
  }

  sealed trait StructNode {
    val name: String
    def fields: Seq[IR.StructField]
  }
  class EmbedNode(val name: String, val children: List[StructNode]) extends StructNode {
    def fields = children.flatMap(_.fields)
  }
  class ValueNode(val name: String, val field: IR.StructField) extends StructNode {
    def fields = Seq(field)
  }

  def createStructTree(
    defn: ResolvedStructDefinition,
    definitions: Map[String, ResolvedStructDefinition],
    structs: Map[String, IR.StructDefinition]
  ): StructTree = {
    val impl = new StructDefImpl(defn.name)

    def resolveType(t: ResolvedType): IR.Type = t match {
      case UnknownType | MissingNamedType(_) | NullType | VoidType => throw new TransformerException("Invalid field type")
      case ResolvedStructType(structName) => throw new TransformerException("Unexpected struct type encountered")

      case ResolvedPointer(valueType) => valueType match {
        case ResolvedStructType(structName) => IR.Type.StructReference(structName, structs.get(structName))
        case _ => IR.Type.Pointer(resolveType(valueType))
      }

      case ResolvedArray(valueType) => valueType match {
        case ResolvedStructType(structName) => IR.Type.Array(IR.Type.StructValue(structs(structName)))
        case _ => IR.Type.Array(resolveType(valueType))
      }

      case IntType => IR.Type.Int
      case StringType => IR.Type.String
      case CharType => IR.Type.Char
      case BoolType => IR.Type.Bool
    }

    def resolveField(field: ResolvedStructField, base: Option[String]): StructNode = {
      val fullName = base.map(_ + "_" + field.name).getOrElse(field.name) // TODO: Avoid conflicting names

      field.valueType match {
        case ResolvedStructType(structName) => {
          new EmbedNode(field.name, definitions(structName).fields.map(fieldDef => resolveField(fieldDef, Some(fullName))))
        }

        case other => new ValueNode(field.name, new IR.StructField(fullName, impl, resolveType(other)))
      }
    }

    val tree = new StructTree(defn.fields.map(resolveField(_, None)), impl)
    impl.updateFields(tree.fields)
    tree
  }

  def createStructMap(definitions: List[ResolvedStructDefinition]): Map[String, StructTree] = {
    val definitionsMap = definitions.map(d => d.name -> d).toMap
    val structMap = definitionsMap.mapValues(d => new StructDefImpl(d.name))
    definitionsMap.mapValues(createStructTree(_, definitionsMap, structMap))
  }

  class GlobalScope(val structs: Map[String, StructTree]) {
    def this(program: ResolvedProgram) = this(createStructMap(program.structDefinitions))

    private def getStructNode(member: ResolvedMember): (ResolvedMember, StructNode) = {
      member.field match {
        case None => throw new TransformerException("Invalid field reference")
        case Some(field) => {
          member.parent match {
            case parent: ResolvedMember if !member.isArrow => {
              val (root, node) = getStructNode(parent)
              node match {
                case embed: EmbedNode => (root, embed.children.find(_.name == field.name).get)
                // Dotted member, but there is no corresponding embedded field
                case _: ValueNode => throw new TransformerException("Invalid dotted field")
              }
            }

            case _ => {
              (member, structs(field.structName).children.find(_.name == field.name).get)
            }
          }
        }
      }
    }

    // Applies struct flattening, returning the "actual" parent expression after flattening
    // and the flattened struct field that is accessed.
    def structMember(member: ResolvedMember): (ResolvedMember, IR.StructField) = {
      val (root, node) = getStructNode(member)
      node match {
        case _: EmbedNode => throw new TransformerException("Cannot directly access embedded struct")
        case value: ValueNode => (root, value.field)
      }
    }

    def varType(resolved: ResolvedType): IR.Type = {
      mapType(resolved) match {
        case Some(t: IR.Type) => t
        case _ => throw new TransformerException("Cannot declare variable of type '" + resolved.name + "'")
      }
    }

    def valueType(resolved: ResolvedType): IR.ValueType = {
      mapType(resolved) match {
        case None => throw new TransformerException("Cannot alloc type '" + resolved.name + "'")
        case Some(typ) => typ
      }
    }

    def returnType(resolved: ResolvedType): Option[IR.Type] = {
      resolved match {
        case VoidType => None
        case _ => Some(varType(resolved))
      }
    }

    def mapType(resolved: ResolvedType): Option[IR.ValueType] = {
      resolved match {
        case UnknownType | MissingNamedType(_) | VoidType | NullType => None
        case ResolvedPointer(ResolvedStructType(structName)) => Some(IR.Type.StructReference(structName, structs.get(structName).map(_.struct)))
        case ResolvedStructType(structName) => structs.get(structName).map(t => IR.Type.StructValue(t.struct))
        case ResolvedPointer(value) => mapType(value).collect { case t: IR.Type => IR.Type.Pointer(t) }
        case ResolvedArray(value) => mapType(value).map(IR.Type.Array(_))
        case IntType => Some(IR.Type.Int)
        case StringType => Some(IR.Type.String)
        case CharType => Some(IR.Type.Char)
        case BoolType => Some(IR.Type.Bool)
      }
    }

    def local() = new LocalScope(structs)
  }

  class LocalScope(
    structs: Map[String, StructTree],
    val variables: ListBuffer[IR.Var] = ListBuffer(),
    val namedVariables: mutable.Map[String, IR.Var] = mutable.Map(),
    val usedNames: mutable.Map[String, Int] = mutable.Map(),
    val nameHint: Option[String] = None
  ) extends GlobalScope(structs) {
    def withName(newName: Option[String]) = new LocalScope(structs, variables, namedVariables, usedNames, newName)

    def varName(hint: Option[String] = nameHint): String = {
      val base = hint.getOrElse("_")
      val (name, number) = usedNames.get(base) match {
        case None => (base, 1)
        case Some(n) => (base + n, n + 1)
      }

      usedNames.update(base, number)
      name
    }

    def allocateTemp(typ: IR.Type) = {
      val variable = new IR.Var(typ, varName())
      variables += variable
      variable
    }

    def allocateNamed(name: String, typ: IR.Type) = {
      val variable = new IR.Var(typ, varName(Some(name)))
      variables += variable
      if (namedVariables.contains(name))
        throw new TransformerException("Duplicate variable name declared")
      namedVariables += (name -> variable)
      variable
    }

    def getVar(variable: Option[ResolvedVariable]): IR.Var = {
      variable.flatMap(v => namedVariables.get(v.name)) match {
        case Some(variable) => variable
        case None => throw new TransformerException("Missing variable")
      }
    }
  }

  // Wraps expression by creating a temp and assigning the value to it
  def wrapExpr(expr: IR.Expr, ops: List[IR.Op], scope: LocalScope): (IR.Var, List[IR.Op]) = {
    val value = expr.valueType match {
      case None => throw new TransformerException("Cannot assign untyped value to variable")
      case Some(valueType) => scope.allocateTemp(valueType)
    }

    (value, ops :+ new IR.Op.AssignVar(value, expr))
  }

  def lowerVar(expr: ResolvedExpression, scope: LocalScope): (IR.Var, List[IR.Op]) = {
    lowerValue(expr, scope) match {
      case (v: IR.Var, ops) => (v, ops)
      case (value, ops) => wrapExpr(value, ops, scope)
    }
  }

  def lowerValue(expr: ResolvedExpression, scope: LocalScope): (IR.Value, List[IR.Op]) = {
    lowerExpression(expr, scope) match {
      case (value: IR.Value, ops) => (value, ops)
      case (expr, ops) => wrapExpr(expr, ops, scope)
    }
  }

  def comparisonOp(operation: ComparisonOperation) = operation match {
    case ComparisonOperation.EqualTo => IR.ComparisonOp.Equal
    case ComparisonOperation.NotEqualTo => IR.ComparisonOp.NotEqual
    case ComparisonOperation.LessThan => IR.ComparisonOp.LessThan
    case ComparisonOperation.LessThanOrEqualTo => IR.ComparisonOp.LessThanEqual
    case ComparisonOperation.GreaterThan => IR.ComparisonOp.GreaterThan
    case ComparisonOperation.GreaterThanOrEqualTo => IR.ComparisonOp.GreaterThanEqual
  }

  def lowerExpression(expr: ResolvedExpression, scope: LocalScope): (IR.Expr, List[IR.Op]) = {
    expr match {
      case ref: ResolvedVariableRef => (scope.getVar(ref.variable), Nil)

      case invoke: ResolvedInvoke => {
        val argExprs = invoke.arguments.map(lowerValue(_, scope))
        val argOps = argExprs.flatMap { case (_, ops) => ops }
        val args = argExprs.map { case (value, _) => value }
        invoke.method match {
          case Some(method) => (new IR.Expr.Invoke(method.name, args, scope.returnType(method.returnType)), argOps)
          case None => throw new TransformerException("Unresolved method")
        }
      }

      case _m: ResolvedMember => {
        val (member, field) = scope.structMember(_m)
        member.parent match {
          case arr: ResolvedArrayIndex if !member.isArrow => {
            val (index, indexOps) = lowerValue(arr.index, scope)
            val (array, arrayOps) = lowerVar(arr.array, scope)
            (new IR.Expr.ArrayFieldAccess(array, index, field), indexOps ++ arrayOps)
          }

          case parent => {
            val ptr = parent match {
              case p if member.isArrow => p
              case deref: ResolvedDereference if !member.isArrow => deref.value
              case _ => throw new TransformerException("Invalid non-pointer member access")
            }

            val (subject, subjectOps) = lowerVar(ptr, scope)
            (new IR.Expr.Member(subject, field), subjectOps)
          }
        }
      }

      case access: ResolvedArrayIndex => {
        val (subject, subjectOps) = lowerVar(access.array, scope)
        val (index, indexOps) = lowerValue(access.index, scope)
        (new IR.Expr.ArrayAccess(subject, index), subjectOps ++ indexOps)
      }

      case _: ResolvedResult =>
        throw new TransformerException("Invalid \\result in method body")

      case _: ResolvedLength =>
        throw new TransformerException("Invalid \\length in method body")

      case _: ResolvedImprecision =>
          throw new TransformerException("Invalid ? expression in method body")

      case _: ResolvedAccessibility =>
        throw new TransformerException("Invalid acc() in method body")

      case arith: ResolvedArithmetic => {
        val (left, leftOps) = lowerValue(arith.left, scope)
        val (right, rightOps) = lowerValue(arith.right, scope)
        val operator = arith.operation match {
          case ArithmeticOperation.Add => IR.ArithmeticOp.Add
          case ArithmeticOperation.Subtract => IR.ArithmeticOp.Subtract
          case ArithmeticOperation.Divide => IR.ArithmeticOp.Divide
          case ArithmeticOperation.Multiply => IR.ArithmeticOp.Multiply
        }

        (new IR.Expr.Arithmetic(left, right, operator), leftOps ++ rightOps)
      }

      case comp: ResolvedComparison => {
        val (left, leftOps) = lowerValue(comp.left, scope)
        val (right, rightOps) = lowerValue(comp.right, scope)
        val operator = comparisonOp(comp.operation)
        (new IR.Expr.Comparison(left, right, operator), leftOps ++ rightOps)
      }

      case ternary: ResolvedTernary => {
        // Rewrite ternary to use assignment in if/else
        val (condition, conditionOps) = lowerValue(ternary.condition, scope)
        ternary.valueType match {
          case NullType => {
            // Both sides of ternary evaluate to NULL, which cannot be saved to a temporary variable
            // Evaluate side-effects inside an if and return a NULL literal
            val (_, ifTrue) = lowerValue(ternary.ifTrue, scope)
            val (_, ifFalse) = lowerValue(ternary.ifFalse, scope)
            (IR.Literal.Null, conditionOps :+ new IR.Op.If(condition, new IR.Block(ifTrue), new IR.Block(ifFalse)))
          }
          case _ => {
            val result = scope.allocateTemp(scope.varType(ternary.valueType))
            val (trueVal, ifTrue) = lowerExpression(ternary.ifTrue, scope)
            val (falseVal, ifFalse) = lowerExpression(ternary.ifFalse, scope)
            val trueBlock = new IR.Block(ifTrue :+ new IR.Op.AssignVar(result, trueVal))
            val falseBlock = new IR.Block(ifFalse :+ new IR.Op.AssignVar(result, falseVal))
            (result, conditionOps :+ new IR.Op.If(condition, trueBlock, falseBlock))
          }
        }
      }

      case logical: ResolvedLogical => {
        // Logical operators are short-circuiting, which introduces branching

        // Introduce a variable that represents the result of evaluating the LHS.
        // Immediately wrap it since we need a temporary variable that can be re-assigned without
        // modifying the original value.
        val (condition, lhsOps) = lowerExpression (logical.left, scope) match {
          case (expr, ops) => wrapExpr(expr, ops, scope)
        }

        val ops = ListBuffer[IR.Op](lhsOps:_*)

        // Negate the condition to check if the RHS needs evaluated
        val negated = scope.allocateTemp(IR.Type.Bool)
        ops += new IR.Op.AssignVar(negated, new IR.Expr.Not(condition))

        // Introduce an If that evaluates the RHS and assigns the result to the variable
        val (rhs, rhsOps) = lowerExpression(logical.right, scope)
        ops += new IR.Op.If(negated, new IR.Block(rhsOps :+ new IR.Op.AssignVar(condition, rhs)), new IR.Block(Nil))

        (condition, ops.toList)
      }

      case deref: ResolvedDereference => lowerVar(deref.value, scope) match {
        case (value, ops) => (new IR.Expr.Deref(value), ops)
      }
      case not: ResolvedNot => lowerValue(not.value, scope) match {
        case (value, ops) => (new IR.Expr.Not(value), ops)
      }
      case negate: ResolvedNegation => lowerValue(negate.value, scope) match {
        case (value, ops) => (new IR.Expr.Negation(value), ops)
      }
      case alloc: ResolvedAllocArray => lowerValue(alloc.length, scope) match {
        case (length, ops) => (new IR.Expr.AllocArray(scope.valueType(alloc.memberType), length), ops)
      }
      case alloc: ResolvedAlloc => (new IR.Expr.Alloc(scope.valueType(alloc.memberType)), Nil)
      case str: ResolvedString => (new IR.Literal.String(str.value), Nil)
      case char: ResolvedChar => (new IR.Literal.Char(char.value), Nil)
      case int: ResolvedInt => (new IR.Literal.Int(int.value), Nil)
      case bool: ResolvedBool => (new IR.Literal.Bool(bool.value), Nil)
      case _: ResolvedNull => (IR.Literal.Null, Nil)
    }
  }

  def lowerStatement(stmt: ResolvedStatement, scope: LocalScope): List[IR.Op] = {
    stmt match {
      case expr: ResolvedExpressionStatement => lowerExpression(expr.value, scope) match {
        case (_: IR.Value, ops) => ops // Simple values can be dropped
        case (value, ops) => ops :+ new IR.Op.Noop(value)
      }

      case assign: ResolvedAssignment => {
        val ops = ListBuffer[IR.Op]()

        // Evaluate RHS first
        assign.left match {
          case ref: ResolvedVariableRef => {
            val namedScope = scope.withName(ref.variable.map(_.name))
            lowerExpression(assign.value, namedScope) match {
              case (expr, exprOps) => exprOps :+ new IR.Op.AssignVar(scope.getVar(ref.variable), expr)
            }
          }

          case _member: ResolvedMember => {
            val (member, field) = scope.structMember(_member)
            val namedScope = scope.withName(Some(_member.fieldName))
            val (value, valueOps) = lowerValue(assign.value, namedScope)

            member.parent match {
              // array[i].field
              case arr: ResolvedArrayIndex if !member.isArrow => {
                // Special-case for non-pointer field access in array
                val (index, indexOps) = lowerValue(arr.index, namedScope)
                val (array, arrayOps) = lowerVar(arr.array, namedScope)
                // Evaluation order: RHS -> Index -> Array -> Assign
                valueOps ++ indexOps ++ arrayOps :+ new IR.Op.AssignArrayMember(array, index, field, value)
              }

              case nonArray => {
                val ptr = nonArray match {
                  case deref: ResolvedDereference if !member.isArrow => deref.value
                  case ptr if member.isArrow => ptr
                  case _ => throw new TransformerException("Invalid member access of non-pointer value")
                }

                val (parent, parentOps) = lowerVar(ptr, namedScope)
                // Evaluation order: RHS -> Parent -> Assign
                valueOps ++ parentOps :+ new IR.Op.AssignMember(parent, field, value)
              }
            }
          }

          case arr: ResolvedArrayIndex => {
            val (value, valueOps) = lowerValue(assign.value, scope)
            val (index, indexOps) = lowerValue(arr.index, scope)
            val (array, arrayOps) = lowerVar(arr.array, scope)
            // Evaluation order: RHS -> Index -> Array
            valueOps ++ indexOps ++ arrayOps :+ new IR.Op.AssignArray(array, index, value)
          }

          case deref: ResolvedDereference => {
            val (value, valueOps) = lowerValue(assign.value, scope)
            val (ptr, ptrOps) = lowerVar(deref.value, scope)
            valueOps ++ ptrOps :+ new IR.Op.AssignPtr(ptr, value)
          }

          case _ => throw new TransformerException("Invalid assignment L-Value")
        }
      }

      case inc: ResolvedIncrement => {
        // Make sure not to evaluate the expression twice
        val one = new IR.Literal.Int(1)
        val operator = inc.operation match {
          case IncrementOperation.Increment => IR.ArithmeticOp.Add
          case IncrementOperation.Decrement => IR.ArithmeticOp.Subtract
        }

        val ops = ListBuffer[IR.Op]()
        // Helper to add the ops to the list and return the value
        def resolve[T](values: (T, List[IR.Op])) = {
          ops ++= values._2
          values._1
        }

        inc.value match {
          case ref: ResolvedVariableRef => {
            val variable = scope.getVar(ref.variable)
            ops += new IR.Op.AssignVar(variable, new IR.Expr.Arithmetic(variable, one, operator))
          }

          case _member: ResolvedMember => {
            val (member, field) = scope.structMember(_member)

            member.parent match {
              // arr[i].field
              case arr: ResolvedArrayIndex if !member.isArrow => {
                val index = resolve(lowerValue(arr.index, scope))
                val array = resolve(lowerVar(arr.array, scope))
                val value = resolve(wrapExpr(new IR.Expr.ArrayFieldAccess(array, index, field), Nil, scope))
                val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
                ops += new IR.Op.AssignArrayMember(array, index, field, incremented)
              }

              case nonArray => {
                val ptr = nonArray match {
                  // (*value).field
                  case deref: ResolvedDereference if !member.isArrow => deref.value
                  // value->field
                  case _ if member.isArrow => nonArray
                  case _ => throw new TransformerException("Invalid non-pointer member access")
                }

                val irPtr = resolve(lowerVar(ptr, scope))
                val value = resolve(wrapExpr(new IR.Expr.Member(irPtr, field), Nil, scope))
                val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
                ops += new IR.Op.AssignMember(irPtr, field, incremented)
              }
            }
          }

          case arr: ResolvedArrayIndex => {
            val index = resolve(lowerValue(arr.index, scope))
            val array = resolve(lowerVar(arr.array, scope))
            val value = resolve(wrapExpr(new IR.Expr.ArrayAccess(array, index), Nil, scope))
            val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
            ops += new IR.Op.AssignArray(array, index, incremented)
          }

          case deref: ResolvedDereference => {
            val ptr = resolve(lowerVar(deref.value, scope))
            val value = resolve(wrapExpr(new IR.Expr.Deref(ptr), Nil, scope))
            val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
            ops += new IR.Op.AssignPtr(ptr, incremented)
          }

          case _ => throw new TransformerException("Invalid increment L-Value")
        }

        ops.toList
      }

      case iff: ResolvedIf => {
        val (condition, conditionOps) = lowerValue(iff.condition, scope)
        val trueBlock = new IR.Block(lowerStatement(iff.ifTrue, scope))
        val falseBlock = new IR.Block(iff.ifFalse.map(lowerStatement(_, scope)).getOrElse(Nil))
        conditionOps :+ new IR.Op.If(condition, trueBlock, falseBlock)
      }

      case whil: ResolvedWhile => {
        // Evaluate condition at start of loop
        val (condition, conditionOps) = lowerValue(whil.condition, scope)
        val invariant = whil.invariant.map(lowerSpec(scope, _)).getOrElse(IR.Spec.True)

        // Evaluate condition at every turn of the loop
        val body = new IR.Block(lowerStatement(whil.body, scope) ++ conditionOps)

        conditionOps :+ new IR.Op.While(condition, invariant, body)
      }

      case ret: ResolvedReturn => {
        ret.value match {
          case None => new IR.Op.Return(None) :: Nil
          case Some(value) => lowerValue(value, scope) match {
            case (retVal, ops) => ops :+ new IR.Op.Return(Some(retVal))
          }
        }
      }

      case assert: ResolvedAssert => lowerValue(assert.value, scope) match {
        case (value, ops) => ops :+ new IR.Op.Assert(value)
      }

      case assert: ResolvedAssertSpecification => {
        List(new IR.Op.AssertSpec(lowerSpec(scope, assert.specification)))
      }

      case error: ResolvedError => lowerValue(error.value, scope) match {
        case (value, ops) => ops :+ new IR.Op.Error(value)
      }

      case block: ResolvedBlock => {
        // Variable scoping is checked before transformation and variable names
        // must be unique across a method, so the named variables can be mutated
        // while transforming a method.
        for (decl <- block.variableDefs) {
          scope.allocateNamed(decl.name, scope.varType(decl.valueType))
        }

        block.statements.flatMap(lowerStatement(_, scope))
      }
    }
  }

  def lowerSpec(scope: LocalScope, spec: ResolvedExpression): IR.Spec = {
    spec match {
      case ref: ResolvedVariableRef => scope.getVar(ref.variable)
      case invoke: ResolvedInvoke => ??? // TODO: Predicate handling
      case member: ResolvedMember => ??? // TODO: field access
      case result: ResolvedResult => new IR.Spec.ReturnValue()


      // TODO: Array handling
      case _: ResolvedArrayIndex => ???
      case _: ResolvedLength => ???

      case arith: ResolvedArithmetic => ???

      case comp: ResolvedComparison => {
        val left = lowerSpec(scope, comp.left)
        val right = lowerSpec(scope, comp.right)
        val op = comparisonOp(comp.operation)
        new IR.Spec.Comparison(left, right, op)
      }

      case ternary: ResolvedTernary => {
        val condition = lowerSpec(scope, ternary.condition)
        val left = lowerSpec(scope, ternary.ifTrue)
        val right = lowerSpec(scope, ternary.ifFalse)
        new IR.Spec.Conditional(condition, left, right)
      }

      case logical: ResolvedLogical => {
        logical.operation match {
          case LogicalOperation.Or => ??? // TODO: Support disjunctions in certain places
          case LogicalOperation.And => new IR.Spec.Conjunction(lowerSpec(scope, logical.left), lowerSpec(scope, logical.right))
        }
      }

      case acc: ResolvedAccessibility => new IR.Spec.Accessibility(lowerFieldAccess(scope, acc.field))
      
      case imprecise: ResolvedImprecision => new IR.Spec.Imprecision()

      case deref: ResolvedDereference => ???
      case not: ResolvedNot => ???
      case negate: ResolvedNegation => ???
      case _: ResolvedAlloc | _: ResolvedAllocArray => throw new TransformerException("Invalid alloc expression in specification")
      case _: ResolvedString => ???
      case _: ResolvedChar => ???
      case int: ResolvedInt => new IR.Literal.Int(int.value)
      case bool: ResolvedBool => new IR.Literal.Bool(bool.value)
      case _: ResolvedNull => ???
    }
  }

  def lowerFieldAccess(scope: LocalScope, expr: ResolvedExpression): IR.FieldAccess = {
    lowerFieldValue(scope, expr) match {
      case access: IR.FieldAccess => access
      case _ => throw new TransformerException("Invalid field")
    }
  }

  def lowerFieldValue(scope: LocalScope, expr: ResolvedExpression): IR.FieldValue = {
    expr match {
      case mem: ResolvedMember => {
        val (member, field) = scope.structMember(mem)
        new IR.FieldAccess.Member(lowerFieldValue(scope, member.parent), field)
      }
      case deref: ResolvedDereference => new IR.FieldAccess.Dereference(lowerFieldValue(scope, deref.value))
      case ref: ResolvedVariableRef => scope.getVar(ref.variable)
      case result: ResolvedResult => new IR.Spec.ReturnValue()
      case _ => throw new TransformerException("Invalid field")
    }
  }

  def methodToIR(method: ResolvedMethodDefinition, scope: LocalScope): IR.MethodImplementation = {
    val args = method.declaration.arguments.map(v => new IR.Var(scope.varType(v.valueType), scope.varName(Some(v.name))))
    for (arg <- args) scope.namedVariables.put(arg.name, arg)

    val precondition = method.declaration.precondition.map(lowerSpec(scope, _)).getOrElse(IR.Spec.True)
    val postcondition = method.declaration.postcondition.map(lowerSpec(scope, _)).getOrElse(IR.Spec.True)
    
    val body = new IR.Block(lowerStatement(method.body, scope))

    // TODO: Implement pre/post-condition rewriting
    new IR.MethodImplementation(
      method.name,
      scope.returnType(method.declaration.returnType),
      args,
      precondition,
      postcondition,
      scope.variables.toList,
      body)
  }

  def programToIR(program: ResolvedProgram): IR.Program = {
    val scope = new GlobalScope(program)
    val methods = program.methodDefinitions.map(d => methodToIR(d, scope.local()))
    val structs = program.structDefinitions.map(s => scope.structs(s.name).struct)
    new IR.Program(methods, structs)
  }

  class StructDefImpl(val name: String) extends IR.StructDefinition
  {
    var _fields: Option[List[IR.StructField]] = None

    def updateFields(fields: List[IR.StructField]): Unit = {
      _fields = Some(fields)
    }

    def fields = _fields.get
  }
}