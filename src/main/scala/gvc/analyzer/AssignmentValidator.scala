package gvc.analyzer

// Validates that LHS of assignments are L-Values and that
// variables are assigned before they are used
object AssignmentValidator {
  case class Scope(errors: ErrorSink, assignedVars: Set[String], postArgs: Set[String]) {
    def assign(ref: ResolvedVariableRef) = ref.variable.map(v => copy(assignedVars = assignedVars + v.name)).getOrElse(this)
    def isAssigned(ref: ResolvedVariableRef) = ref.variable.forall(v => assignedVars.contains(v.name))
    def join(scope: Scope) = copy(assignedVars = assignedVars.intersect(scope.assignedVars))
  }

  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions) {
      validateMethod(errors, method)
    }
  }

  def validateMethod(errors: ErrorSink, method: ResolvedMethodDefinition): Unit = {
    val scope = Scope(
      errors,
      method.declaration.arguments.map(_.name).toSet,
      method.declaration.postcondition.map(ExpressionVisitor.collectVariables(_)).getOrElse(Set.empty)
    )

    validateStatement(scope, method.body)
  }

  def validateStatement(scope: Scope, stmt: ResolvedStatement): Scope = {
    stmt match {
      case expr: ResolvedExpressionStatement => {
        validateExpression(scope, expr.value)
        scope
      }

      case assign: ResolvedAssignment => {
        validateCanAssign(scope, assign.left)

        val newVars = assign.left match {
          case ref: ResolvedVariableRef if assign.operation.isEmpty => scope.assign(ref)
          case _ => {
            validateExpression(scope, assign.left)
            scope
          }
        }

        validateExpression(scope, assign.value)
        newVars
      }

      case inc: ResolvedIncrement => {
        validateCanAssign(scope, inc.value)
        validateExpression(scope, inc.value)
        scope
      }

      case iff: ResolvedIf => {
        validateExpression(scope, iff.condition)
        val trueVars = validateStatement(scope, iff.ifTrue)
        iff.ifFalse.map(f => trueVars.join(validateStatement(scope, f))).getOrElse(scope)
      }

      case whil: ResolvedWhile => {
        validateExpression(scope, whil.condition)
        whil.invariant.map(validateExpression(scope, _))
        validateStatement(scope, whil.body)
        scope
      }

      case ret: ResolvedReturn => {
        ret.value.foreach(validateExpression(scope, _))
        scope
      }

      case assert: ResolvedAssert => {
        validateExpression(scope, assert.value)
        scope
      }

      case error: ResolvedError => {
        validateExpression(scope, error.value)
        scope
      }

      case block: ResolvedBlock => {
        var blockScope = scope
        block.statements.takeWhile { stmt =>
          blockScope = validateStatement(blockScope, stmt)
          stmt match {
            case _: ResolvedReturn | _: ResolvedError => false
            case _ => true
          }
        }

        blockScope
      }
    }
  }

  def validateExpression(scope: Scope, expr: ResolvedExpression): Unit = {
    ExpressionVisitor.visit(expr, {
      case ref: ResolvedVariableRef if !scope.isAssigned(ref) => {
        scope.errors.error(ref, "Uninitialized variable '" + ref.variable.map(_.name).getOrElse("") + "'")
        true
      }

      case _ => true
    })
  }

  def validateCanAssign(scope: Scope, expr: ResolvedExpression): Unit = {
    expr match {
      case ref: ResolvedVariableRef =>
        ref.variable
          .map(v => v.name)
          .filter(scope.postArgs.contains(_))
          .foreach(v => scope.errors.error(ref, "Cannot assign to variable '" + v + "' used in @ensures annotation"))
      case _ => ()
    }

    validateLValue(scope.errors, expr)
  }

  def validateLValue(errors: ErrorSink, expr: ResolvedExpression): Unit = {
    expr match {
      case ref: ResolvedVariableRef => ()
      case member: ResolvedMember => validateLValue(errors, member.parent)
      case index: ResolvedArrayIndex => validateLValue(errors, index.array)
      case deref: ResolvedDereference => validateLValue(errors, deref.value)
      case _ => {
        errors.error(expr, "Invalid subject of assignment")
      }
    }
  }
}