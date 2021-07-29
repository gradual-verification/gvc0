package gvc.analyzer
import scala.collection.mutable.{ListBuffer, HashMap}

// Validates that all methods and predicates used are defined, that methods do
// not use expressions valid only in predicates, and that predicates are valid
// specifications.
object ImplementationValidator {
  def validate(program: ResolvedProgram, errors: ErrorSink): ResolvedProgram = {
    val invokes = new InvokeScanner()
    program.methodDeclarations.foreach(invokes.declaration)
    program.methodDefinitions.foreach(invokes.definition)

    val defined = program.methodDefinitions.toSeq.map(d => (d.name, d)).toMap

    for ((name, calls) <- invokes.methods) {
      defined.get(name) match {
        case Some(definition) => validateMethod(definition.body, errors)
        case None => calls.foreach(call => errors.error(call, s"'${call.methodName}' is not defined"))
      }
    }

    for ((name, calls) <- invokes.predicates) {
      defined.get(name) match {
        case Some(definition) => validatePredicate(definition.body, errors)
        case None => calls.foreach(call => errors.error(call, s"'${call.methodName}' is not defined"))
      }
    }

    if (!defined.contains("main")) {
      errors.programError("'main' method not defined")
    }

    program
  }

  class InvokeScanner {
    val methods = HashMap[String, ListBuffer[ResolvedInvoke]]().withDefault(_ => ListBuffer[ResolvedInvoke]())
    val predicates = HashMap[String, ListBuffer[ResolvedInvoke]]().withDefault(_ => ListBuffer[ResolvedInvoke]())

    def declaration(decl: ResolvedMethodDeclaration) = {
      decl.precondition.foreach(verify)
      decl.postcondition.foreach(verify)
    }

    def definition(method: ResolvedMethodDefinition) = {
      statement(method.body)
    }

    def statement(stmt: ResolvedStatement): Unit = {
      stmt match {
        case x: ResolvedExpressionStatement => execute(x.value)
        case x: ResolvedAssignment => {
          execute(x.left)
          execute(x.value)
        }
        case x: ResolvedIncrement => execute(x.value)
        case x: ResolvedIf => {
          execute(x.condition)
          statement(x.ifTrue)
          x.ifFalse.foreach(statement)
        }
        case x: ResolvedWhile => {
          execute(x.condition)
          x.invariant.foreach(verify)
          statement(x.body)
        }
        case x: ResolvedReturn => x.value.foreach(execute)
        case x: ResolvedAssert => execute(x.value)
        case x: ResolvedAssertSpecification => verify(x.specification)
        case x: ResolvedError => execute(x.value)
        case x: ResolvedBlock => x.statements.foreach(statement)
      }
    }

    def execute(expr: ResolvedExpression) = ExpressionVisitor.visit(expr, collectMethods)
    def verify(expr: ResolvedExpression) = ExpressionVisitor.visit(expr, collectPredicates)

    def collectMethods(expr: ResolvedExpression): Unit = {
      expr match {
        case invoke: ResolvedInvoke if invoke.method.isDefined => {
          val method = invoke.method.get
          methods.getOrElseUpdate(method.name, ListBuffer()) += invoke
        }

        case _ => ()
      }
    }

    def collectPredicates(expr: ResolvedExpression): Unit = {
      expr match {
        case invoke: ResolvedInvoke if invoke.method.isDefined => {
          val method = invoke.method.get
          predicates.getOrElseUpdate(method.name, ListBuffer()) += invoke
        }

        case _ => ()
      }
    }
  }

  // Scan expressions used in statements but not specifications
  def validateMethod(stmt: ResolvedStatement, errors: ErrorSink): Unit = {
    val (statements, expressions) = stmt match {
      case x: ResolvedExpressionStatement => (Seq.empty, Seq(x.value))
      case x: ResolvedAssignment => (Seq.empty, Seq(x.left, x.value))
      case x: ResolvedIncrement => (Seq.empty, Seq(x.value))
      case x: ResolvedIf => (Seq(x.ifTrue) ++ x.ifFalse, Seq(x.condition))
      case x: ResolvedWhile => (Seq(x.body), Seq(x.condition))
      case x: ResolvedReturn => (Seq.empty, x.value.toSeq)
      case x: ResolvedAssert => (Seq.empty, Seq(x.value))
      case _: ResolvedAssertSpecification => (Seq.empty, Seq.empty)
      case x: ResolvedError => (Seq.empty, Seq(x.value))
      case x: ResolvedBlock => (x.statements, Seq.empty)
    }

    expressions.foreach(ExpressionVisitor.visit(_, _ match {
      case acc: ResolvedAccessibility => errors.error(acc, "Cannot use acc() expressions in method called during execution")
      case _ => ()
    }))

    statements.foreach(validateMethod(_, errors))
  }

  def validatePredicate(body: ResolvedBlock, errors: ErrorSink) = body.statements match {
    case (ret: ResolvedReturn) :: Nil if ret.value.isDefined =>
      SpecificationValidator.validateSpecification(ret.value.get, errors)
    case other :: _ =>
      errors.error(other, "Method used as predicate must contain only a single return statement")
    case Nil =>
      errors.error(body, "Method used as predicate must contain a return statement")
  }
}