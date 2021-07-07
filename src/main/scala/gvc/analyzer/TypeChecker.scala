package gvc.analyzer
import scala.collection.mutable.HashMap

object TypeChecker {
  def check(program: ResolvedProgram, errors: ErrorSink): Unit = {
    checkMethodDeclarations(program, errors)
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