package gvc.analyzer
import scala.collection.mutable.HashMap

object TypeChecker {
  def check(program: ResolvedProgram, errors: ErrorSink): Unit = {
    checkMethodDeclarations(program, errors)
    checkMethods(program, errors)
  }

  def checkMethodDeclarations(program: ResolvedProgram, errors: ErrorSink): Unit = {
    val initialDecls = HashMap[String, ResolvedMethodDeclaration]()

    for (decl <- program.methodDeclarations) {
      initialDecls.get(decl.name) match {
        case Some(initial) =>
          if (!compatibleDeclarations(initial, decl))
            errors.error(decl, "Mismatching types for function '" + decl.name + "'")
        case None =>
          initialDecls += (decl.name -> decl)
      }

      val invalidParams = decl.arguments.filterNot(arg => validDefinitionType(arg.valueType))
      for (arg <- invalidParams) {
        errors.error(arg, "Invalid parameter type: " + arg.valueType.toString())
      }
    }
  }

  def checkMethods(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions) {
      checkStatement(errors, method.declaration, method.body)
    }
  }

  def checkStatement(errors: ErrorSink,  method: ResolvedMethodDeclaration, statement: ResolvedStatement): Unit = {
    statement match {
      case expr: ResolvedExpressionStatement => checkExpression(errors, expr.value)

      case assign: ResolvedAssignment => {
        checkExpression(errors, assign.value)
        assertEquivalent(errors, assign.left, assign.value)
      }

      case incr: ResolvedIncrement => checkExpression(errors, incr.value)

      case iff: ResolvedIf => {
        checkExpression(errors, iff.condition)
        assertType(errors, iff.condition, BoolType)

        checkStatement(errors, method, iff.ifTrue)
        iff.ifFalse.map(checkStatement(errors, method, _))
      }

      case whil: ResolvedWhile => {
        checkExpression(errors, whil.condition)
        assertType(errors, whil.condition, BoolType)

        whil.invariant match {
          case None => ()
          case Some(invariant) => {
            checkExpression(errors, invariant)
            assertType(errors, invariant, BoolType)
          }
        }

        checkStatement(errors, method, whil.body)
      }

      case ret: ResolvedReturn => {
        ret.value match {
          case None => {
            if (method.returnType != VoidType) {
              errors.error(ret, "Must return a value from a non-void method")
            }
          }

          case Some(value) => {
            checkExpression(errors, value)
            assertType(errors, value, method.returnType)
          }
        }
      }

      case assert: ResolvedAssert => {
        checkExpression(errors, assert.value)
        assertType(errors, assert.value, BoolType)
      }

      case error: ResolvedError => {
        checkExpression(errors, error.value)
        assertType(errors, error.value, StringType)
      }

      case block: ResolvedBlock => {
        val invalidVars = block.variableDefs.filterNot(v => validDefinitionType(v.valueType))
        for (variable <- invalidVars) {
          errors.error(variable, "Invalid variable type: " + variable.valueType.toString())
        }

        for (stmt <- block.statements)
          checkStatement(errors, method, stmt)
      }
    }
  }

  def checkExpression(errors: ErrorSink, expression: ResolvedExpression): Unit = {
    expression match {
      case _: ResolvedVariableRef => ()

      case invoke: ResolvedInvoke => {
        for (arg <- invoke.arguments)
          checkExpression(errors, arg)
        
        invoke.method match {
          case None => ()
          case Some(method) => {
            if (method.arguments.length != invoke.arguments.length) {
              errors.error(invoke, "Invalid number of arguments passed to '" + invoke.methodName + "'")
            } else {
              for ((defn, arg) <- method.arguments zip invoke.arguments) {
                assertType(errors, arg, defn.valueType)
              }
            }
          }
        }
      }

      case member: ResolvedMember => checkExpression(errors, member.parent)

      case index: ResolvedArrayIndex => {
        checkExpression(errors, index.array)
        checkExpression(errors, index.index)

        index.array.valueType match {
          case _: ResolvedArray => ()
          case t => errors.error(index.array, "Expected array type, encountered '" + t.toString() + "'")
        }

        assertType(errors, index.index, IntType)
      }

      case ar: ResolvedArithmetic => {
        checkExpression(errors, ar.left)
        checkExpression(errors, ar.right)
        assertType(errors, ar.left, IntType)
        assertType(errors, ar.right, IntType)
      }

      case comp: ResolvedComparison => {
        checkExpression(errors, comp.left)
        checkExpression(errors, comp.right)
        assertEquivalent(errors, comp.left, comp.right)
      }

      case ternary: ResolvedTernary => {
        checkExpression(errors, ternary.condition)
        checkExpression(errors, ternary.ifTrue)
        checkExpression(errors, ternary.ifFalse)
        assertType(errors, ternary.condition, BoolType)

        // TODO: Narrow type from null?
        assertEquivalent(errors, ternary.ifTrue, ternary.ifFalse)
      }

      case logical: ResolvedLogical => {
        checkExpression(errors, logical.left)
        checkExpression(errors, logical.right)
        assertType(errors, logical.left, BoolType)
        assertType(errors, logical.right, BoolType)
      }

      case deref: ResolvedDereference => {
        checkExpression(errors, deref.value)
        deref.value.valueType match {
          case ResolvedPointer(_) => ()
          case typ => errors.error(deref, "Dereferencing non-pointer type '" + typ.toString() + "'")
        }
      }

      case not: ResolvedNot => {
        checkExpression(errors, not.value)
        assertType(errors, not.value, BoolType)
      }

      case negate: ResolvedNegation => {
        checkExpression(errors, negate.value)
        assertType(errors, negate, IntType)
      }

      case alloc: ResolvedAlloc => checkAlloc(errors, alloc, alloc.memberType)

      case alloc: ResolvedAllocArray => {
        checkExpression(errors, alloc.length)
        checkAlloc(errors, alloc, alloc.memberType)
        assertType(errors, alloc.length, IntType)
      }

      case _: ResolvedString |
        _: ResolvedChar |
        _: ResolvedInt |
        _: ResolvedBool |
        _: ResolvedNull => ()
    }
  }

  def checkAlloc(errors: ErrorSink, stmt: ResolvedExpression, typ: ResolvedType): Unit = {
    if (!validDefinitionType(typ)) {
      errors.error(stmt, "Invalid type: " + typ.toString())
    }
  }

  def assertEquivalent(errors: ErrorSink, left: ResolvedExpression, right: ResolvedExpression) = {
    assertNonVoid(errors, left)
    assertType(errors, right, left.valueType)
  }

  def assertNonVoid(errors: ErrorSink, expr: ResolvedExpression): Unit = {
    if (expr.valueType == VoidType) {
      errors.error(expr, "Invalid value: void type")
    }
  }

  def assertType(errors: ErrorSink, expr: ResolvedExpression, expectedType: ResolvedType): Unit = {
    if (!expectedType.isEquivalent(expr.valueType)) {
      errors.error(expr, "Invalid value: expected type '" + expectedType.toString() + "' but encountered '" + expr.valueType.toString() + "'")
    }
  }

  def compatibleDeclarations(initial: ResolvedMethodDeclaration, current: ResolvedMethodDeclaration): Boolean = {
    return initial.arguments.length == current.arguments.length &&
      initial.returnType.isEquivalent(current.returnType) &&
      initial.arguments.zip(current.arguments).forall { case (iArg, cArg) => iArg.valueType.isEquivalent(cArg.valueType) }
  }

  def validDefinitionType(t: ResolvedType): Boolean = {
    t match {
      case ResolvedPointer(valueType) => validDefinitionType(valueType)
      case ResolvedArray(valueType) => validDefinitionType(valueType)
      case NullType | VoidType => false
      case _ => true
    }
  }
}