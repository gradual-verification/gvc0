package gvc.transformer

import gvc.analyzer._
import scala.collection.mutable.ListBuffer

class TransformerException(val message: String) extends RuntimeException

object Transformer {
  def methodToIR(method: ResolvedMethodDefinition, program: ResolvedProgram): IR.MethodImplementation = {
    val variables = ListBuffer[IR.Var]()
    var scope = Map[String, IR.Var]()
    var currentBlock = ListBuffer[IR.Op]()
    var currentName: Option[String] = None

    def withBlock(evaluator: () => Unit): IR.Block = {
      val oldBlock = currentBlock
      currentBlock = ListBuffer()
      evaluator()

      val block = new IR.Block(currentBlock.toList)
      currentBlock = oldBlock
      block
    }

    def withName[T](name: Option[String], action: () => T): T = {
      val oldName = currentName
      currentName = name
      val result = action()
      currentName = oldName
      result
    }

    def lowerExpression(expr: ResolvedExpression): IR.Expr = {
      expr match {
        case ref: ResolvedVariableRef => getVar(ref.variable)

        case invoke: ResolvedInvoke => {
          val args = invoke.arguments.map(lowerValue(_))
          invoke.method match {
            case Some(method) => new IR.Expr.Invoke(method.name, args, getType(method.returnType))
            case None => throw new TransformerException("Unresolved method")
          }
        }

        case member: ResolvedMember => {
          val (fieldName, fieldType) = getField(member)
          member.parent match {
            case arr: ResolvedArrayIndex if !member.isArrow => {
              val index = lowerValue(arr.index)
              val array = lowerVar(arr.array)
              new IR.Expr.ArrayFieldAccess(array, index, fieldName, fieldType)
            }

            case parent => {
              val ptr = parent match {
                case p if member.isArrow => p
                case deref: ResolvedDereference if !member.isArrow => deref.value
                case _ => throw new TransformerException("Invalid non-pointer member access")
              }

              val subject = lowerVar(ptr)
              new IR.Expr.Member(subject, fieldName, fieldType)
            }
          }
        }

        case index: ResolvedArrayIndex => {
          val subject = lowerVar(index.array)
          val idx = lowerValue(index.index)
          new IR.Expr.ArrayAccess(subject, idx)
        }

        case _: ResolvedResult =>
          throw new TransformerException("Invalid \\result in method body")

        case _: ResolvedLength =>
          throw new TransformerException("Invalid \\length in method body")

        case arith: ResolvedArithmetic => {
          val (left, right) = (lowerValue(arith.left), lowerValue(arith.right))
          new IR.Expr.Arithmetic(left, right, arith.operation match {
            case ArithmeticOperation.Add => IR.ArithmeticOp.Add
            case ArithmeticOperation.Subtract => IR.ArithmeticOp.Subtract
            case ArithmeticOperation.Divide => IR.ArithmeticOp.Divide
            case ArithmeticOperation.Multiply => IR.ArithmeticOp.Multiply
          })
        }

        case comp: ResolvedComparison => {
          val (left, right) = (lowerValue(comp.left), lowerValue(comp.right))
          new IR.Expr.Comparison(left, right, comp.operation match {
            case ComparisonOperation.EqualTo => IR.ComparisonOp.Equal
            case ComparisonOperation.NotEqualTo => IR.ComparisonOp.NotEqual
            case ComparisonOperation.LessThan => IR.ComparisonOp.LessThan
            case ComparisonOperation.LessThanOrEqualTo => IR.ComparisonOp.LessThanEqual
            case ComparisonOperation.GreaterThan => IR.ComparisonOp.GreaterThan
            case ComparisonOperation.GreaterThanOrEqualTo => IR.ComparisonOp.GreaterThanEqual
          })
        }

        case ternary: ResolvedTernary => {
          // Rewrite ternary to use assignment in if/else
          val condition = lowerValue(ternary.condition)
          ternary.valueType match {
            case NullType => {
              // Both sides of ternary evaluate to NULL, which cannot be saved to a temporary variable
              // Evaluate side-effects inside an if and return a NULL literal
              val trueBlock = withBlock { () => lowerValue(ternary.ifTrue) }
              val falseBlock = withBlock { () => lowerValue(ternary.ifFalse) }
              currentBlock += new IR.Op.If(condition, trueBlock, falseBlock)
              IR.Literal.Null
            }
            case _ => {
              val result = declareVar(getVarType(ternary.valueType))
              val trueBlock = withBlock { () =>
                currentBlock += new IR.Op.AssignVar(result, lowerExpression(ternary.ifTrue))
              }
              val falseBlock = withBlock { () =>
                currentBlock += new IR.Op.AssignVar(result, lowerExpression(ternary.ifFalse))
              }

              currentBlock += new IR.Op.If(condition, trueBlock, falseBlock)
              result
            }
          }
        }

        case logical: ResolvedLogical => {
          val (left, right) = (lowerValue(logical.left), lowerValue(logical.right))
          new IR.Expr.Logical(left, right, logical.operation match {
            case LogicalOperation.Or => IR.LogicalOp.Or
            case LogicalOperation.And => IR.LogicalOp.And
          })
        }

        case deref: ResolvedDereference => new IR.Expr.Deref(lowerVar(deref.value))
        case not: ResolvedNot => new IR.Expr.Not(lowerValue(not.value))
        case negate: ResolvedNegation => new IR.Expr.Negation(lowerValue(negate.value))
        case alloc: ResolvedAlloc => new IR.Expr.Alloc(getAllocType(alloc.memberType))
        case alloc: ResolvedAllocArray => new IR.Expr.AllocArray(getAllocType(alloc.memberType), lowerValue(alloc.length))
        case str: ResolvedString => new IR.Literal.String(str.value)
        case char: ResolvedChar => new IR.Literal.Char(char.value)
        case int: ResolvedInt => new IR.Literal.Int(int.value)
        case bool: ResolvedBool => new IR.Literal.Bool(bool.value)
        case _: ResolvedNull => IR.Literal.Null
      }
    }

    def declareVar(varType: IR.Type, nameHint: Option[String] = currentName): IR.Var = {
      val variable = new IR.Var(varType, nameHint)
      variables += variable
      variable
    }

    def toValue(expr: IR.Expr): IR.Value = {
      expr match {
        case value: IR.Value => value
        case complex => complex.valueType match {
          case None => throw new TransformerException("Cannot assign untyped value to variable")
          case Some(valueType) => {
            val irVar = declareVar(valueType)
            currentBlock += new IR.Op.AssignVar(irVar, complex)
            irVar
          }
        }
      }
    }

    def toVar(expr: IR.Expr): IR.Var = {
      toValue(expr) match {
        case v: IR.Var => v
        case _ => throw new TransformerException("Expected variable but encounted literal")
      }
    }

    def lowerValue(expr: ResolvedExpression): IR.Value = {
      toValue(lowerExpression(expr))
    }

    def lowerVar(expr: ResolvedExpression): IR.Var = {
      toVar(lowerExpression(expr))
    }

    def lowerStatement(stmt: ResolvedStatement): Unit = {
      stmt match {
        case expr: ResolvedExpressionStatement => {
          currentBlock += new IR.Op.Noop(lowerExpression(expr.value))
        }

        case assign: ResolvedAssignment => {
          // Evaluate RHS first
          assign.left match {
            case ref: ResolvedVariableRef => {
              withName(ref.variable.map(_.name), () => {
                val value = lowerExpression(assign.value)
                currentBlock += new IR.Op.AssignVar(getVar(ref.variable), value)
              })
            }

            case member: ResolvedMember => {
              withName(Some(member.fieldName), () => {
                val value = lowerValue(assign.value)

                member.parent match {
                  // array[i].field
                  case arr: ResolvedArrayIndex if !member.isArrow => {
                    // Special-case for non-pointer field access in array
                    val index = lowerValue(arr.index)
                    val array = lowerVar(arr.array)
                    currentBlock += new IR.Op.AssignArrayMember(array, index, member.fieldName, value)
                  }

                  case nonArray => {
                    val ptr = nonArray match {
                      case deref: ResolvedDereference if !member.isArrow => deref.value
                      case ptr if member.isArrow => ptr
                      case _ => throw new TransformerException("Invalid member access of non-pointer value")
                    }

                    currentBlock += new IR.Op.AssignMember(lowerVar(ptr), member.fieldName, value)
                  }
                }
              })
            }

            case arr: ResolvedArrayIndex => {
              // Evaluation order: RHS -> Index -> Array
              val value = lowerValue(assign.value)
              val index = lowerValue(arr.index)
              currentBlock += new IR.Op.AssignArray(lowerVar(arr.array), index, value)
            }

            case deref: ResolvedDereference => {
              val value = lowerValue(assign.value)
              currentBlock += new IR.Op.AssignPtr(lowerVar(deref.value), value)
            }

            case _ => throw new TransformerException("Invalid assignment L-Value")
          }
        }

        case inc: ResolvedIncrement => {
          // Make sure not to evaluate the expression twice
          val one = new IR.Literal.Int(1)
          val op = inc.operation match {
            case IncrementOperation.Increment => IR.ArithmeticOp.Add
            case IncrementOperation.Decrement => IR.ArithmeticOp.Subtract
          }

          inc.value match {
            case ref: ResolvedVariableRef => {
              val variable = getVar(ref.variable)
              currentBlock += new IR.Op.AssignVar(variable, new IR.Expr.Arithmetic(variable, one, op))
            }

            case member: ResolvedMember => {
              val (fieldName, fieldType) = getField(member)
              member.parent match {
                // arr[i].field
                case arr: ResolvedArrayIndex if !member.isArrow => {
                  val index = lowerValue(arr.index)
                  val array = lowerVar(arr.array)
                  val value = toValue(new IR.Expr.ArrayFieldAccess(array, index, fieldName, fieldType))
                  val incremented = toValue(new IR.Expr.Arithmetic(value, one, op))
                  currentBlock += new IR.Op.AssignArrayMember(array, index, fieldName, incremented)
                }

                case nonArray => {
                  val ptr = nonArray match {
                    // (*value).field
                    case deref: ResolvedDereference if !member.isArrow => deref.value
                    // value->field
                    case _ if member.isArrow => nonArray
                    case _ => throw new TransformerException("Invalid non-pointer member access")
                  }

                  val irPtr = lowerVar(ptr)
                  val value = toValue(new IR.Expr.Member(irPtr, fieldName, fieldType))
                  val incremented = toValue(new IR.Expr.Arithmetic(value, one, op))
                  currentBlock += new IR.Op.AssignMember(irPtr, fieldName, incremented)
                }
              }
            }

            case arr: ResolvedArrayIndex => {
              val index = lowerValue(arr.index)
              val array = lowerVar(arr.array)
              val value = toValue(new IR.Expr.ArrayAccess(array, index))
              val incremented = toValue(new IR.Expr.Arithmetic(value, one, op))
              currentBlock += new IR.Op.AssignArray(array, index, value)
            }

            case deref: ResolvedDereference => {
              val ptr = lowerVar(deref.value)
              val value = toValue(new IR.Expr.Deref(ptr))
              val incremented = toValue(new IR.Expr.Arithmetic(value, one, op))
              currentBlock += new IR.Op.AssignPtr(ptr, incremented)
            }

            case _ => throw new TransformerException("Invalid increment L-Value")
          }
        }

        case iff: ResolvedIf => {
          val condition = lowerValue(iff.condition)
          val trueBlock = withBlock { () => lowerStatement(iff.ifTrue) }
          val falseBlock = iff.ifFalse
            .map(ifFalse => withBlock(() => lowerStatement(ifFalse)))
            .getOrElse(new IR.Block(List.empty))
          currentBlock += new IR.Op.If(condition, trueBlock, falseBlock)
        }

        case whil: ResolvedWhile => {
          // TODO: Transform invariant

          // Evaluate condition at start of loop
          val condition = declareVar(IR.Type.Bool)
          currentBlock += new IR.Op.AssignVar(condition, lowerExpression(whil.condition))

          val body = withBlock { () =>
            lowerStatement(whil.body)
            // Evaluate condition at every turn of the loop
            currentBlock += new IR.Op.AssignVar(condition, lowerExpression(whil.condition))
          }

          currentBlock += new IR.Op.While(condition, body)
        }

        case ret: ResolvedReturn => {
          val value = ret.value.map(lowerValue)
          currentBlock += new IR.Op.Return(value)
        }

        // TODO: Implement assert
        case assert: ResolvedAssert => ()

        case error: ResolvedError => {
          val value = lowerValue(error.value)
          currentBlock += new IR.Op.Error(value)
        }

        case block: ResolvedBlock => {
          val oldScope = scope
          scope = scope ++ block.variableDefs.map(d => (d.name, declareVar(getVarType(d.valueType), Some(d.name))))

          for (stmt <- block.statements) {
            lowerStatement(stmt)
          }

          scope = oldScope
        }
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

    def getField(member: ResolvedMember): (String, IR.Type) = {
      member.field match {
        case None => throw new TransformerException("Unresolved struct field")
        case Some(field) => (field.name, getVarType(field.valueType))
      }
    }

    def getVar(variable: Option[ResolvedVariable]): IR.Var = {
      variable.flatMap(v => scope.get(v.name)) match {
        case Some(variable) => variable
        case None => throw new TransformerException("Missing variable")
      }
    }

    val args = method.declaration.arguments.map(v => new IR.Var(getVarType(v.valueType), Some(v.name)))
    scope = scope ++ args.map(a => (a.nameHint.get, a))
    lowerStatement(method.body)

    // TODO: Implement pre/post-condition rewriting
    new IR.MethodImplementation(
      method.name,
      getType(method.declaration.returnType),
      args,
      variables.toList,
      new IR.Block(currentBlock.toList))
  }
}