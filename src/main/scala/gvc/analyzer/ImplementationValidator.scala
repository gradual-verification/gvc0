package gvc.analyzer

import scala.annotation.tailrec

// Validates that all methods and predicates used are defined, that methods do
// not use expressions valid only in predicates, and that predicates are valid
// specifications.
object ImplementationValidator {

  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    val definedMethods = program.methodDefinitions.toSeq.map(_.name).toSet
    val libraryMethods = collectLibraryMethods(program.dependencies, errors)
    val definedPredicates = program.predicateDefinitions.toSeq.map(_.name).toSet
    if (!definedMethods.contains("main")) {
      errors.programError("'main' method not defined")
    }

    def expression(expr: ResolvedExpression): Unit = {
      ExpressionVisitor.visit(
        expr,
        _ match {
          case invoke: ResolvedInvoke => invoke.method.foreach { m =>
            if (!libraryMethods.contains(m.name) && !definedMethods.contains(m.name))
              errors.error(invoke, s"'${invoke.methodName}' is never implemented")
          }

          case pred: ResolvedPredicate
              if pred.predicate.isDefined && !definedPredicates
                .contains(pred.predicate.get.name) => {
            errors.error(pred, s"'${pred.predicateName}' is never implemented")
          }

          case _ => ()
        }
      )
    }

    def statement(stmt: ResolvedStatement): Unit = {
      stmt match {
        case x: ResolvedExpressionStatement => expression(x.value)
        case x: ResolvedAssignment => {
          expression(x.left)
          expression(x.value)
        }
        case x: ResolvedIncrement => expression(x.value)
        case x: ResolvedIf => {
          expression(x.condition)
          statement(x.ifTrue)
          x.ifFalse.foreach(statement)
        }
        case x: ResolvedWhile => {
          expression(x.condition)
          statement(x.body)
        }
        case x: ResolvedReturn => x.value.foreach(expression)
        case x: ResolvedAssert => expression(x.value)
        case x: ResolvedAssertSpecification =>
          () // Abstract predicates allowed in asserts
        case x: ResolvedError           => expression(x.value)
        case x: ResolvedBlock           => x.statements.foreach(statement)
        case x: ResolvedUnfoldPredicate => expression(x.predicate)
        case x: ResolvedFoldPredicate   => expression(x.predicate)
      }
    }

    // Abstract predicates allowed in pre/post-conditions and other predicates
    // Only check predicates in folds/unfolds

    program.methodDefinitions.foreach(m => statement(m.body))
  }

  @tailrec
  def collectLibraryMethods(
      uses: List[ResolvedUseDeclaration],
      errors: ErrorSink,
      methods: Set[String] = Set(),
      visitedLibraries: Set[String] = Set()
  ): Set[String] = {
    uses match {
      case Nil => methods
      case use :: rest => use.dependency match {
        case Some(program) if !visitedLibraries.contains(use.name) =>
          program.methodDefinitions.foreach(defn =>
            errors.error(defn, "Imported libraries may not contain method implementations"))
          program.predicateDefinitions.foreach(defn =>
            errors.error(defn, "Imported libraries may not contain predicate implementations"))
          program.structDefinitions.foreach(defn =>
            errors.error(defn, "Imported libraries may not contain struct definitions"))

          // TODO: Allow abstract predicates to be imported? - yes - JD
          //program.predicateDeclarations.foreach(defn =>
            //errors.error(defn, "Imported predicates are not implemented"))

          collectLibraryMethods(
            program.dependencies ::: rest,
            errors,
            methods ++ program.methodDeclarations.map(_.name),
            visitedLibraries + use.name
          )
        case _ => collectLibraryMethods(rest, errors, methods, visitedLibraries)
      }
    }
  }
}
