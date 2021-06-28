package gvc.parser
import fastparse._

trait Statements extends Specifications {
  sealed trait ConcreteStatement;

  def statement[_: P]: P[Statement] =
    P(annotations ~ concreteStatement).map({
      case (annot, concrete) => concrete.withSpecifications(annot)
    })

  def concreteStatement[_: P]: P[Statement] =
    P(
      blockStatement |
      ifStatement |
      whileStatement |
      forStatement |
      returnStatement |
      assertStatement |
      errorStatement |
      (simpleStatement ~ ";")
    )

  def blockStatement[_: P]: P[BlockStatement] =
    P("{" ~ annotations ~ (statement.rep(1) ~ annotations).? ~ "}")
    .map({
      case (post, None) => BlockStatement(List.empty, List.empty, post)
      case (pre, Some((stmts, post))) => stmts.toList match {
        case head :: tl => BlockStatement(head.withSpecifications(pre ++ head.specifications) :: tl, List.empty, post)
        case Nil => ??? // This should be impossible since no statements would result in None
      }
    })
  
  def ifStatement[_: P]: P[IfStatement] =
    P("if" ~ "(" ~ expression ~ ")" ~ statement ~ ("else" ~ statement).?).map({
      case (condition, body, els) => IfStatement(condition, body, els)
    })
  
  def whileStatement[_: P]: P[WhileStatement] =
    P("while" ~ "(" ~ expression ~ ")" ~ statement).map({
      case (condition, body) => WhileStatement(condition, body)
    })

  def forStatement[_: P]: P[ForStatement] =
    P("for" ~ "(" ~/ simpleStatement ~ ";" ~ expression ~ ";" ~ simpleStatement ~ ")" ~ statement).map({
      case (init, condition, next, body) => ForStatement(init, condition, next, body)
    })

  def returnStatement[_: P]: P[ReturnStatement] =
    P("return" ~ expression.? ~ ";").map(ReturnStatement(_))

  def assertStatement[_: P]: P[AssertStatement] =
    P("assert" ~ "(" ~ expression ~ ")" ~ ";").map(AssertStatement(_))
  
  def errorStatement[_: P]: P[ErrorStatement] =
    P("error" ~ "(" ~ expression ~ ")" ~ ";").map(ErrorStatement(_))

  def simpleStatement[_: P]: P[Statement] =
    P(variableStatement | expressionStatement)

  def variableStatement[_: P]: P[VariableStatement] =
    P(typeReference ~ identifier ~ ("=" ~ expression).?).map({
      case (varType, varName, value) => VariableStatement(varType, varName, value)
    })

  def expressionStatement[_: P]: P[Statement] = P(expression ~/ statementTail.?)
    .map({
      case (expr, None) => ExpressionStatement(expr)
      case (expr, Some(PostfixTail(op))) => UnaryOperationStatement(expr, op)
      case (expr, Some(AssignmentTail(op, value))) => AssignmentStatement(expr, op, value)
    })

  sealed trait StatementTail
  case class PostfixTail(op: UnaryOperator.Value) extends StatementTail
  case class AssignmentTail(op: AssignOperator.Value, value: Expression) extends StatementTail

  def statementTail[_: P]: P[StatementTail] = P(postfixTail | assignmentTail)

  def postfixTail[_: P]: P[PostfixTail] = P(postfixOperator.!)
    .map({
      case "++" => PostfixTail(UnaryOperator.Increment)
      case "--" => PostfixTail(UnaryOperator.Decrement)
    })

  def assignmentTail[_: P]: P[AssignmentTail] = P(assignmentOperator.! ~ expression)
    .map({
      case (assignOp, value) => AssignmentTail(parseAssignOperator(assignOp), value)
    })

  def parseAssignOperator(op: String): AssignOperator.Value = {
    import AssignOperator._
    op match {
      case "=" => Assign
      case "+=" => Add
      case "-=" => Subtract
      case "*=" => Multiply
      case "/=" => Divide
      case "%=" => Modulus
      case "<<=" => ShiftLeft
      case ">>=" => ShiftRight
      case "&=" => BitwiseAnd
      case "^=" => BitwiseXor
      case "|=" => BitwiseOr
    }
  }
}