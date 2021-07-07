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
      checkStatement(method.body, errors)
    }
  }

  def checkStatement(statement: ResolvedStatement, errors: ErrorSink): Unit = {
    statement match {
      case expr: ResolvedExpressionStatement => checkExpression(expr.value)
      case assign: ResolvedAssignment => checkExpression(assign.value)
      case incr: ResolvedIncrement => checkExpression(incr.value)

      case iff: ResolvedIf => {
        checkStatement(iff.ifTrue, errors)
        iff.ifFalse.map(checkStatement(_, errors))
      }

      case whil: ResolvedWhile => {
        checkExpression(whil.condition)
        whil.invariant.map(checkExpression(_))
        checkStatement(whil.body, errors)
      }

      case ret: ResolvedReturn => ret.value.map(checkExpression)
      case assert: ResolvedAssert => checkExpression(assert.value)
      case error: ResolvedError => checkExpression(error.value)

      case block: ResolvedBlock => {
        val invalidVars = block.variableDefs.filterNot(v => validDefinitionType(v.valueType))
        for (variable <- invalidVars) {
          errors.error(variable, "Invalid variable type: " + variable.valueType.toString())
        }

        for (stmt <- block.statements)
          checkStatement(stmt, errors)
      }
    }
  }

  def checkExpression(expression: ResolvedExpression): Unit = {

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