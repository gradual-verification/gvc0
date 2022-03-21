package gvc.analyzer

// Validates that all methods and predicates used are defined, that methods do
// not use expressions valid only in predicates, and that predicates are valid
// specifications.
object ImplementationValidator {

  def validate(program: ResolvedProgram, errors: ErrorSink): Unit = {
    val definedMethods = program.methodDefinitions.toSeq.map(_.name).toSet
    val definedPredicates = program.predicateDefinitions.toSeq.map(_.name).toSet
    if (!definedMethods.contains("main")) {
      errors.programError("'main' method not defined")
    }

    def expression(expr: ResolvedExpression): Unit = {
      ExpressionVisitor.visit(
        expr,
        _ match {
          case invoke: ResolvedInvoke
              if invoke.method.isDefined && !invoke.method.get.fromHeader && !definedMethods
                .contains(invoke.method.get.name) => {
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
}
