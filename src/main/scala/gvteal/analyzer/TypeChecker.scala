package gvteal.analyzer
import scala.collection.mutable.HashMap
import gvteal.analyzer.ComparisonOperation.EqualTo
import gvteal.analyzer.ComparisonOperation.NotEqualTo
import gvteal.analyzer.ComparisonOperation.LessThan
import gvteal.analyzer.ComparisonOperation.GreaterThan
import gvteal.analyzer.ComparisonOperation.GreaterThanOrEqualTo
import gvteal.analyzer.ComparisonOperation.LessThanOrEqualTo

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
          if (!initial.returnType.isEquivalent(decl.returnType) || !compatibleArguments(initial.arguments, decl.arguments))
            errors.error(decl, s"Mismatched types for method '${decl.name}'")
        case None =>
          initialDecls += (decl.name -> decl)
      }

      val invalidParams = decl.arguments.filterNot(arg => validDefinitionType(arg.valueType))
      for (arg <- invalidParams) {
        errors.error(arg, "Invalid parameter type: " + arg.valueType.name)
      }
    }
  }

  def checkMethods(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions) {
      method.declaration.precondition.foreach(checkExpression(errors, _))
      method.declaration.postcondition.foreach(checkExpression(errors, _))
      checkStatement(errors, method.declaration, method.body)
    }
  }

  def checkPredicateDeclarations(program: ResolvedProgram, errors: ErrorSink): Unit = {
    val initialDecls = HashMap[String, ResolvedPredicateDeclaration]()

    for (decl <- program.predicateDeclarations) {
      initialDecls.get(decl.name) match {
        case Some(initial) if !compatibleArguments(initial.arguments, decl.arguments) =>
            errors.error(decl, s"Mismatched types for predicate '${decl.name}'")
        case None => initialDecls += (decl.name -> decl)
        case _ => ()
      }

      val invalidParams = decl.arguments.filterNot(arg => validDefinitionType(arg.valueType))
      for (arg <- invalidParams) {
        errors.error(arg, "Invalid parameter type: " + arg.valueType.name)
      }
    }
  }

  def checkPredicates(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (pred <- program.predicateDefinitions) {
      checkExpression(errors, pred.body)
    }
  }

  def checkStatement(errors: ErrorSink,  method: ResolvedMethodDeclaration, statement: ResolvedStatement): Unit = {
    statement match {
      case expr: ResolvedExpressionStatement => {
        checkExpression(errors, expr.value)
        assertSmall(errors, expr.value)
      }

      case assign: ResolvedAssignment => {
        checkExpression(errors, assign.value)
        assertSmall(errors, assign.value)
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
        whil.invariant.foreach(checkExpression(errors, _))
        checkStatement(errors, method, whil.body)
      }

      case ret: ResolvedReturn => {
        ret.value match {
          case None => {
            if (method.returnType != VoidType) {
              errors.error(ret, "Must return a value from a non-void method")
            }
          }

          case Some(value) if method.returnType == VoidType => {
            errors.error(ret, "Cannot return a value from a void method")
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

      case assert: ResolvedAssertSpecification => {
        checkExpression(errors, assert.specification)
        assertType(errors, assert.specification, BoolType)
      }

      case fold: ResolvedFoldPredicate => checkExpression(errors, fold.predicate)
      case unfold: ResolvedUnfoldPredicate => checkExpression(errors, unfold.predicate)

      case error: ResolvedError => {
        checkExpression(errors, error.value)
        assertType(errors, error.value, StringType)
      }

      case block: ResolvedBlock => {
        val invalidVars = block.variableDefs.filterNot(v => validDefinitionType(v.valueType))
        for (variable <- invalidVars) {
          errors.error(variable, "Invalid variable type: " + variable.valueType.name)
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
              errors.error(invoke, s"Invalid number of arguments passed to '${invoke.methodName}'")
            } else {
              for ((defn, arg) <- method.arguments zip invoke.arguments) {
                assertType(errors, arg, defn.valueType)
              }
            }
          }
        }
      }

      case predicate: ResolvedPredicate => {
        for (arg <- predicate.arguments)
          checkExpression(errors, arg)
        
        predicate.predicate match {
          case None => ()
          case Some(decl) => {
            if (decl.arguments.length != predicate.arguments.length) {
              errors.error(predicate, s"Invalid number of arguments passed to '${predicate.predicateName}'")
            } else {
              for ((defn, arg) <- decl.arguments zip predicate.arguments) {
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
          case t => errors.error(index.array, "Expected array type, encountered '" + t.name + "'")
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
        comp.operation match {
          case EqualTo | NotEqualTo =>
            assertEquality(errors, comp.left, comp.right)
          case NotEqualTo | LessThan | GreaterThan | GreaterThanOrEqualTo | LessThanOrEqualTo =>
            assertComparison(errors, comp.left, comp.right)
        }
      }

      case ternary: ResolvedTernary => {
        checkExpression(errors, ternary.condition)
        checkExpression(errors, ternary.ifTrue)
        checkExpression(errors, ternary.ifFalse)
        assertType(errors, ternary.condition, BoolType)

        assertSmall(errors, ternary.ifTrue)
        assertSmall(errors, ternary.ifFalse)
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
          case typ => errors.error(deref, "Dereferencing non-pointer type '" + typ.name + "'")
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

      case alloc: ResolvedAlloc => assertAlloc(errors, alloc, alloc.memberType)

      case alloc: ResolvedAllocArray => {
        checkExpression(errors, alloc.length)
        assertAlloc(errors, alloc, alloc.memberType)
        assertType(errors, alloc.length, IntType)
      }

      case length: ResolvedLength => {
        checkExpression(errors, length.array)
        length.array.valueType match {
          case _: ResolvedArray => ()
          case other => {
            errors.error(length, "Expected array type, encountered '" + other.name + "'")
          }
        }
      }

      case acc: ResolvedAccessibility => {
        // Disregard the actual type of the field, just make sure it is a field/deref
        assertField(errors, acc.field)
      }

      case _: ResolvedResult |
        _: ResolvedImprecision |
        _: ResolvedString |
        _: ResolvedChar |
        _: ResolvedInt |
        _: ResolvedBool |
        _: ResolvedNull => ()
    }
  }

  def assertAlloc(errors: ErrorSink, stmt: ResolvedExpression, typ: ResolvedType): Unit = {
    if (!nonVoidType(typ)) {
      errors.error(stmt, "Invalid type: " + typ.name)
    }
  }

  def assertSmall(errors: ErrorSink, value: ResolvedExpression): Unit = {
    if (!smallType(value.valueType))
      errors.error(value, "Type '" + value.valueType.name + "' is not small")
  }

  val FIELD_ERROR = "Subject of acc() expression must be a field or dereference"
  
  def assertField(errors: ErrorSink, expr: ResolvedExpression): Unit = {
    // Top-level must not be simply a variable, but can contain a nested variable
    expr match {
      case _: ResolvedVariableRef | _: ResolvedResult => errors.error(expr, FIELD_ERROR)
      case _ => assertFieldInner(errors, expr)
    }
  }

  def assertFieldInner(errors: ErrorSink, expr: ResolvedExpression): Unit = {
    expr match {
      case _: ResolvedVariableRef | _: ResolvedResult => ()
      case member: ResolvedMember => assertFieldInner(errors, member.parent)
      case deref: ResolvedDereference => assertFieldInner(errors, deref.value)
      case _ => errors.error(expr, FIELD_ERROR)
    }
  }

  def assertEquivalent(errors: ErrorSink, left: ResolvedExpression, right: ResolvedExpression): Unit = {
    assertNonVoid(errors, left)
    assertType(errors, right, left.valueType)
  }

  def assertEquality(errors: ErrorSink, left: ResolvedExpression, right: ResolvedExpression): Unit = {
    // "Operators == and != apply to types int, bool, char, t [], and t *"
    if (assertValidEquality(errors, left) && assertValidEquality(errors, right))
      assertEquivalent(errors, left, right)
  }

  def assertValidEquality(errors: ErrorSink, value: ResolvedExpression): Boolean = {
    value.valueType match {
      case UnknownType | IntType | BoolType | CharType | NullType | ResolvedArray(_) | ResolvedPointer(_) => true
      case other => {
        errors.error(value, "Invalid value, expected int, bool, char, array, or pointer, but encountered '" + other.name + "'")
        false
      }
    }
  }

  def assertComparison(errors: ErrorSink, left: ResolvedExpression, right: ResolvedExpression) = {
    // "Operators <, <=, >=, and > apply to types int and char"
    if (assertValidComparison(errors, left) && assertValidComparison(errors, right))
      assertEquivalent(errors, left, right)
  }

  def assertValidComparison(errors: ErrorSink, value: ResolvedExpression) = {
    value.valueType match {
      case UnknownType | IntType | CharType => true
      case other => {
        errors.error(value, "Invalid value, expected int or char but encountered '" + other.name + "'")
        false
      }
    }
  }

  def assertNonVoid(errors: ErrorSink, expr: ResolvedExpression): Unit = {
    if (expr.valueType == VoidType) {
      errors.error(expr, "Invalid value: void type")
    }
  }

  def assertType(errors: ErrorSink, expr: ResolvedExpression, expectedType: ResolvedType): Unit = {
    if (!expectedType.isEquivalent(expr.valueType)) {
      errors.error(expr, s"Invalid value: expected type '${expectedType.name}' but encountered '${expr.valueType.name}'")
    }
  }

  def compatibleArguments(initial: List[ResolvedVariable], current: List[ResolvedVariable]): Boolean = {
    return initial.length == current.length &&
      initial.zip(current).forall { case (iArg, cArg) => iArg.valueType.isEquivalent(cArg.valueType) }
  }

  def validDefinitionType(t: ResolvedType): Boolean = smallType(t) && nonVoidType(t)

  def smallType(t: ResolvedType): Boolean = {
    t match {
      case _: ResolvedStructType => false
      case _ => true
    }
  }

  def nonVoidType(t: ResolvedType): Boolean = {
    t match {
      case ResolvedPointer(valueType) => nonVoidType(valueType)
      case ResolvedArray(valueType) => nonVoidType(valueType)
      case NullType | VoidType => false
      case _ => true
    }
  }
}