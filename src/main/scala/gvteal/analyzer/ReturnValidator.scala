package gvteal.analyzer

import scala.annotation.tailrec

object ReturnValidator {
  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    validateReturn(program, errors)

    // TODO: Do we want to check for early returns?
    // validateTailReturn(program, errors)
  }

  // Adds an error for any early return from a method
  // Implemented because gotos and returns are not implemented in GV Viper
  def validateTailReturn(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions)
      validateTailReturn(method.body, true, errors)
  }

  def validateTailReturn(stmt: ResolvedStatement, last: Boolean, errors: ErrorSink): Unit = {
    stmt match {
      case ret: ResolvedReturn if !last => {
        errors.error(ret, "Early returns are unsupported")
      }

      case iff: ResolvedIf => {
        validateTailReturn(iff.ifTrue, last, errors)
        iff.ifFalse.map(validateTailReturn(_, last, errors))
      }

      case whil: ResolvedWhile => {
        validateTailReturn(whil.body, last, errors)
      }

      case block: ResolvedBlock => {
        @tailrec
        def check(remaining: List[ResolvedStatement]): Unit = {
          remaining match {
            case Nil => ()
            case head :: Nil => validateTailReturn(head, last, errors)
            case head :: rest => {
              validateTailReturn(head, false, errors)
              check(rest)
            }
          }
        }

        check(block.statements)
      }

      case _ => ()
    }
  }

  def validateReturn(program: ResolvedProgram, errors: ErrorSink): Unit = {
    for (method <- program.methodDefinitions.filter(_.declaration.returnType != VoidType)) {
      if (!checkReturn(method.body)) {
        errors.error(method.declaration, "Not all code paths of '" + method.declaration.name + "' return a value")
      }
    }
  }

  def checkReturn(stmt: ResolvedStatement): Boolean = {
    stmt match {
      case _: ResolvedReturn => true
      case _: ResolvedError => true
      // If statements can only be counted if both sides are defined and return a value
      case iff: ResolvedIf => iff.ifFalse.isDefined && checkReturn(iff.ifTrue) && checkReturn(iff.ifFalse.get)
      case block: ResolvedBlock => block.statements.exists(checkReturn(_))
      // While bodies are not guaranteed to execute, so do not include them in the analysis
      case _ => false
    }
  }
}