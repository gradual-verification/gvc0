package gvc.analyzer

// Validates that LHS of assignments are L-Values and that
// variables are assigned before they are used
object AssignmentValidator {
  type VariableBag = Set[String]

  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions) {
      validateMethod(errors, method)
    }
  }

  def validateMethod(errors: ErrorSink, method: ResolvedMethodDefinition): Unit = {
    val variables = method.declaration.arguments.map(_.name).toSet
    validateStatement(errors, variables, method.body)
  }

  def validateStatement(errors: ErrorSink, assignedVars: VariableBag, stmt: ResolvedStatement): VariableBag = {
    var vars = assignedVars

    stmt match {
      case expr: ResolvedExpressionStatement => {
        validateExpression(errors, assignedVars, expr.value)
        assignedVars
      }

      case assign: ResolvedAssignment => {
        val newVars = assign.left match {
          case ref: ResolvedVariableRef if assign.operation.isEmpty => {
            ref.variable match {
              case None => assignedVars
              case Some(value) => assignedVars + value.name
            }
          }
          case _ => {
            validateLValue(errors, assign.left)
            validateExpression(errors, assignedVars, assign.left)
            assignedVars
          }
        }

        validateExpression(errors, assignedVars, assign.value)
        newVars
      }

      case inc: ResolvedIncrement => {
        validateExpression(errors, assignedVars, inc.value)
        assignedVars
      }

      case iff: ResolvedIf => {
        validateExpression(errors, assignedVars, iff.condition)
        val trueVars = validateStatement(errors, assignedVars, iff.ifTrue)
        iff.ifFalse match {
          case None => assignedVars
          case Some(falseStmt) => {
            // Add variables that are assigned in both the true and false statement
            val falseVars = validateStatement(errors, assignedVars, falseStmt)
            trueVars.intersect(falseVars)
          }
        }
      }

      case whil: ResolvedWhile => {
        validateExpression(errors, assignedVars, whil.condition)
        whil.invariant.map(validateExpression(errors, assignedVars, _))
        validateStatement(errors, assignedVars, whil.body)
        assignedVars
      }

      case ret: ResolvedReturn => {
        ret.value.map(validateExpression(errors, assignedVars, _))
        assignedVars
      }

      case assert: ResolvedAssert => {
        validateExpression(errors, assignedVars, assert.value)
        assignedVars
      }

      case error: ResolvedError => {
        validateExpression(errors, assignedVars, error.value)
        assignedVars
      }

      case block: ResolvedBlock => {
        var vars = assignedVars
        var returned = false
        for (stmt <- block.statements) {
          if (!returned) {
            vars = validateStatement(errors, vars, stmt)
            returned = stmt.isInstanceOf[ResolvedReturn] || stmt.isInstanceOf[ResolvedError]
          }
        }

        vars
      }
    }
  }

  def validateExpression(errors: ErrorSink, assignedVars: VariableBag, expr: ResolvedExpression): Unit = {
    ExpressionVisitor.visit(expr, {
      case ref: ResolvedVariableRef => {
        ref.variable match {
          case Some(variable) if !assignedVars.contains(variable.name) => {
            errors.error(ref, "Uninitialized variable '" + variable.name + "'")
          }
          case _ => ()
        }
        true
      }

      case _ => true
    })
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