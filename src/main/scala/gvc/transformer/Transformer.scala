package gvc.transformer

import gvc.analyzer._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable

class TransformerException(val message: String) extends RuntimeException

object Transformer {
  class Scope(
    val variables: ListBuffer[IR.Var],
    val namedVariables: mutable.Map[String, IR.Var],
    val nameHint: Option[String]
  ) {
    def this() = this(ListBuffer(), mutable.Map(), None)
    def withName(newName: Option[String]) = new Scope(variables, namedVariables, newName)

    def allocateTemp(typ: IR.Type) = {
      val variable = new IR.Var(typ, nameHint)
      variables += variable
      variable
    }

    def allocateNamed(name: String, typ: IR.Type) = {
      val variable = new IR.Var(typ, Some(name))
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

  def getField(member: ResolvedMember): (String, IR.Type) = {
    member.field match {
      case None => throw new TransformerException("Unresolved struct field")
      case Some(field) => (field.name, getVarType(field.valueType))
    }
  }

  def getVarType(resolved: ResolvedType): IR.Type = {
    getType(resolved) match {
      case None => throw new TransformerException("Cannot declare variable of type '" + resolved.name + "'")
      case Some(IR.Type.Struct(_)) => throw new TransformerException("Cannot declare variable of struct type")
      case Some(typ) => typ
    }
  }

  def getAllocType(resolved: ResolvedType): IR.Type = {
    getType(resolved) match {
      case None => throw new TransformerException("Cannot alloc type '" + resolved.name + "'")
      case Some(typ) => typ
    }
  }
  
  def getType(resolved: ResolvedType): Option[IR.Type] = {
    resolved match {
      case UnknownType | MissingNamedType(_) | VoidType | NullType => None
      case ResolvedStructType(structName) => Some(IR.Type.Struct(structName))
      case ResolvedPointer(valueType) => getType(valueType).map(IR.Type.Pointer(_))
      case ResolvedArray(valueType) => getType(valueType).map(IR.Type.Array(_))
      case IntType => Some(IR.Type.Int)
      case StringType => Some(IR.Type.String)
      case CharType => Some(IR.Type.Char)
      case BoolType => Some(IR.Type.Bool)
    }
  }

  // Wraps expression by creating a temp and assigning the value to it
  def wrapExpr(expr: IR.Expr, ops: List[IR.Op], scope: Scope): (IR.Var, List[IR.Op]) = {
    val value = expr.valueType match {
      case None => throw new TransformerException("Cannot assign untyped value to variable")
      case Some(valueType) => scope.allocateTemp(valueType)
    }

    (value, ops :+ new IR.Op.AssignVar(value, expr))
  }

  def lowerVar(expr: ResolvedExpression, scope: Scope): (IR.Var, List[IR.Op]) = {
    lowerValue(expr, scope) match {
      case (v: IR.Var, ops) => (v, ops)
      case (value, ops) => wrapExpr(value, ops, scope)
    }
  }

  def lowerValue(expr: ResolvedExpression, scope: Scope): (IR.Value, List[IR.Op]) = {
    lowerExpression(expr, scope) match {
      case (value: IR.Value, ops) => (value, ops)
      case (expr, ops) => wrapExpr(expr, ops, scope)
    }
  }

  def lowerExpression(expr: ResolvedExpression, scope: Scope): (IR.Expr, List[IR.Op]) = {
    expr match {
      case ref: ResolvedVariableRef => (scope.getVar(ref.variable), Nil)

      case invoke: ResolvedInvoke => {
        val argExprs = invoke.arguments.map(lowerValue(_, scope))
        val argOps = argExprs.flatMap { case (_, ops) => ops }
        val args = argExprs.map { case (value, _) => value }
        invoke.method match {
          case Some(method) => (new IR.Expr.Invoke(method.name, args, getType(method.returnType)), argOps)
          case None => throw new TransformerException("Unresolved method")
        }
      }

      case member: ResolvedMember => {
        val (fieldName, fieldType) = getField(member)
        member.parent match {
          case arr: ResolvedArrayIndex if !member.isArrow => {
            val (index, indexOps) = lowerValue(arr.index, scope)
            val (array, arrayOps) = lowerVar(arr.array, scope)
            (new IR.Expr.ArrayFieldAccess(array, index, fieldName, fieldType), indexOps ++ arrayOps)
          }

          case parent => {
            val ptr = parent match {
              case p if member.isArrow => p
              case deref: ResolvedDereference if !member.isArrow => deref.value
              case _ => throw new TransformerException("Invalid non-pointer member access")
            }

            val (subject, subjectOps) = lowerVar(ptr, scope)
            (new IR.Expr.Member(subject, fieldName, fieldType), subjectOps)
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
        val operator = comp.operation match {
          case ComparisonOperation.EqualTo => IR.ComparisonOp.Equal
          case ComparisonOperation.NotEqualTo => IR.ComparisonOp.NotEqual
          case ComparisonOperation.LessThan => IR.ComparisonOp.LessThan
          case ComparisonOperation.LessThanOrEqualTo => IR.ComparisonOp.LessThanEqual
          case ComparisonOperation.GreaterThan => IR.ComparisonOp.GreaterThan
          case ComparisonOperation.GreaterThanOrEqualTo => IR.ComparisonOp.GreaterThanEqual
        }

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
            val result = scope.allocateTemp(getVarType(ternary.valueType))
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
        case (length, ops) => (new IR.Expr.AllocArray(getAllocType(alloc.memberType), length), ops)
      }
      case alloc: ResolvedAlloc => (new IR.Expr.Alloc(getAllocType(alloc.memberType)), Nil)
      case str: ResolvedString => (new IR.Literal.String(str.value), Nil)
      case char: ResolvedChar => (new IR.Literal.Char(char.value), Nil)
      case int: ResolvedInt => (new IR.Literal.Int(int.value), Nil)
      case bool: ResolvedBool => (new IR.Literal.Bool(bool.value), Nil)
      case _: ResolvedNull => (IR.Literal.Null, Nil)
    }
  }

  def lowerStatement(stmt: ResolvedStatement, scope: Scope): List[IR.Op] = {
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

          case member: ResolvedMember => {
            val namedScope = scope.withName(Some(member.fieldName))
            val (value, valueOps) = lowerValue(assign.value, namedScope)

            member.parent match {
              // array[i].field
              case arr: ResolvedArrayIndex if !member.isArrow => {
                // Special-case for non-pointer field access in array
                val (index, indexOps) = lowerValue(arr.index, namedScope)
                val (array, arrayOps) = lowerVar(arr.array, namedScope)
                // Evaluation order: RHS -> Index -> Array -> Assign
                valueOps ++ indexOps ++ arrayOps :+ new IR.Op.AssignArrayMember(array, index, member.fieldName, value)
              }

              case nonArray => {
                val ptr = nonArray match {
                  case deref: ResolvedDereference if !member.isArrow => deref.value
                  case ptr if member.isArrow => ptr
                  case _ => throw new TransformerException("Invalid member access of non-pointer value")
                }

                val (parent, parentOps) = lowerVar(ptr, namedScope)
                // Evaluation order: RHS -> Parent -> Assign
                valueOps ++ parentOps :+ new IR.Op.AssignMember(parent, member.fieldName, value)
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

          case member: ResolvedMember => {
            val (fieldName, fieldType) = getField(member)

            member.parent match {
              // arr[i].field
              case arr: ResolvedArrayIndex if !member.isArrow => {
                val index = resolve(lowerValue(arr.index, scope))
                val array = resolve(lowerVar(arr.array, scope))
                val value = resolve(wrapExpr(new IR.Expr.ArrayFieldAccess(array, index, fieldName, fieldType), Nil, scope))
                val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
                ops += new IR.Op.AssignArrayMember(array, index, fieldName, incremented)
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
                val value = resolve(wrapExpr(new IR.Expr.Member(irPtr, fieldName, fieldType), Nil, scope))
                val incremented = resolve(wrapExpr(new IR.Expr.Arithmetic(value, one, operator), Nil, scope))
                ops += new IR.Op.AssignMember(irPtr, fieldName, incremented)
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
        // TODO: Transform invariant

        // Evaluate condition at start of loop
        val (condition, conditionOps) = lowerValue(whil.condition, scope)

        // Evaluate condition at every turn of the loop
        val body = new IR.Block(lowerStatement(whil.body, scope) ++ conditionOps)

        conditionOps :+ new IR.Op.While(condition, body)
      }

      case ret: ResolvedReturn => {
        ret.value match {
          case None => new IR.Op.Return(None) :: Nil
          case Some(value) => lowerValue(value, scope) match {
            case (retVal, ops) => ops :+ new IR.Op.Return(Some(retVal))
          }
        }
      }

      // TODO: Implement assert
      case assert: ResolvedAssert => Nil

      case error: ResolvedError => lowerValue(error.value, scope) match {
        case (value, ops) => ops :+ new IR.Op.Error(value)
      }

      case block: ResolvedBlock => {
        // Variable scoping is checked before transformation and variable names
        // must be unique across a method, so the named variables can be mutated
        // while transforming a method.
        for (decl <- block.variableDefs) {
          scope.allocateNamed(decl.name, getVarType(decl.valueType))
        }

        block.statements.flatMap(lowerStatement(_, scope))
      }
    }
  }

  def methodToIR(method: ResolvedMethodDefinition, program: ResolvedProgram): IR.MethodImplementation = {
    val scope = new Scope()
    val args = method.declaration.arguments.map(v => new IR.Var(getVarType(v.valueType), Some(v.name)))
    for (arg <- args) scope.namedVariables += (arg.nameHint.get -> arg)
    
    val body = new IR.Block(lowerStatement(method.body, scope))

    // TODO: Implement pre/post-condition rewriting
    new IR.MethodImplementation(
      method.name,
      getType(method.declaration.returnType),
      args,
      scope.variables.toList,
      body)
  }
}