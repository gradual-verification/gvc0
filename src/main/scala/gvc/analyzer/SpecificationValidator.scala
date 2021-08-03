package gvc.analyzer

// Validates the structure of specifications
// This could be integrated into the type-checker since it arguably is checking
// the types of values used in specifications
object SpecificationValidator {
  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    program.methodDeclarations.foreach(validateDeclaration(_, errors))
    program.predicateDefinitions.foreach(validatePredicate(_, errors))
  }

  def validateDeclaration(decl: ResolvedMethodDeclaration, errors: ErrorSink): Unit = {
    decl.precondition.map(validateSpecification(_, errors, imprecisionAllowed = true))
    decl.postcondition.map(validateSpecification(_, errors, imprecisionAllowed = true))
  }

  def validatePredicate(decl: ResolvedPredicateDefinition, errors: ErrorSink): Unit = {
    validateSpecification(decl.body, errors, imprecisionAllowed = true)
  }

  def validateSpecification(spec: ResolvedExpression, errors: ErrorSink, imprecisionAllowed: Boolean = false): Unit = {
    spec match {
      case _: ResolvedVariableRef => ()
      case _: ResolvedResult => ()
      case _: ResolvedBool => ()
      
      case predicate: ResolvedPredicate => {
        predicate.arguments.foreach(validateValue(_, errors))
      }

      case imp: ResolvedImprecision if imprecisionAllowed => ()
      case imp: ResolvedImprecision => {
        // TODO: Better error message
        errors.error(imp, "? can only be used as the left value of a top-level conjunction")
      }
      
      case member: ResolvedMember => validateField(member.parent, errors)
      case acc: ResolvedAccessibility => validateField(acc.field, errors)
      case deref: ResolvedDereference => validateField(deref.value, errors)

      case comp: ResolvedComparison => {
        validateValue(comp.left, errors)
        validateValue(comp.right, errors)
      }

      case ternary: ResolvedTernary => {
        validateValue(ternary.condition, errors)
        validateSpecification(ternary.ifTrue, errors)
        validateSpecification(ternary.ifFalse, errors)
      }

      case logical: ResolvedLogical => {
        // OR expressions can only contain values
        // AND expressions can contain anything in an expression
        logical.operation match {
          case LogicalOperation.Or => {
            validateValue(logical.left, errors)
            validateValue(logical.right, errors)
          }

          case LogicalOperation.And => {
            validateSpecification(logical.left, errors, imprecisionAllowed)
            validateSpecification(logical.right, errors)
          }
        }
      }

      case not: ResolvedNot => validateValue(not.value, errors)

      case _: ResolvedAlloc | _: ResolvedAllocArray => {
        errors.error(spec, "Invalid alloc in specification")
      }

      case _: ResolvedArrayIndex | _: ResolvedLength => {
        errors.error(spec, "Array access in specifications is not implemented")
      }

      case _: ResolvedNull
        | _: ResolvedInt
        | _: ResolvedChar
        | _: ResolvedString
        | _: ResolvedNegation
        | _: ResolvedArithmetic
        | _: ResolvedInvoke => {
        errors.error(spec, "Invalid value in specification")
      }
    }
  }

  // Validates a value used in an expression
  // Must not escape back to validateSpecification for a nested value
  def validateValue(value: ResolvedExpression, errors: ErrorSink): Unit = {
    value match {
      case _: ResolvedVariableRef
        | _: ResolvedResult
        | _: ResolvedChar
        | _: ResolvedInt
        | _: ResolvedBool
        | _: ResolvedNull => ()

      case invoke: ResolvedInvoke => {
        errors.error(value, "Invalid method call in specification value")
        invoke.arguments.foreach(validateValue(_, errors))
      }

      case predicate: ResolvedPredicate => {
        errors.error(value, "Invalid predicate in specification value. Predicates may only be used in specifications, not as values.")
        predicate.arguments.foreach(validateValue(_, errors))
      }

      case member: ResolvedMember => validateField(member.parent, errors)

      case _: ResolvedArrayIndex | _: ResolvedLength => {
        errors.error(value, "Array access in specifications is not implemented")
      }

      case _: ResolvedAccessibility => {
        errors.error(value, "Invalid acc() expression used as a value")
      }

      case _: ResolvedImprecision => {
        errors.error(value, "Invalid ? expression used as a value")
      }

      case arith: ResolvedArithmetic => {
        validateValue(arith.left, errors)
        validateValue(arith.right, errors)
      }

      case comp: ResolvedComparison => {
        validateValue(comp.left, errors)
        validateValue(comp.right, errors)
      }

      case ternary: ResolvedTernary => {
        validateValue(ternary.condition, errors)
        validateValue(ternary.ifTrue, errors)
        validateValue(ternary.ifFalse, errors)
      }

      case logical: ResolvedLogical => {
        validateValue(logical.left, errors)
        validateValue(logical.right, errors)
      }

      case deref: ResolvedDereference => {
        validateField(deref.value, errors)
      }

      case not: ResolvedNot => validateValue(not.value, errors)

      case negate: ResolvedNegation => validateValue(negate.value, errors)

      case _: ResolvedAlloc => {
        errors.error(value, "Invalid alloc in specification")
      }

      case alloc: ResolvedAllocArray => {
        errors.error(alloc, "Invalid alloc in specification")
        validateValue(alloc.length, errors)
      }

      case str: ResolvedString => {
        errors.error(str, "String values are not implemented in specifications")
      }
    }
  }

  def validateField(value: ResolvedExpression, errors: ErrorSink): Unit = {
    value match {
      case _: ResolvedVariableRef | _: ResolvedResult => ()
      case member: ResolvedMember => validateField(member.parent, errors)
      case deref: ResolvedDereference => validateField(deref.value, errors)

      case _ => {
        errors.error(value, "Invalid value in specification, expected field")
      }
    }
  }
}