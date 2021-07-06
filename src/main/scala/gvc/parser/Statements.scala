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
      (simpleStatement ~/ ";")
    )

  def blockStatement[_: P]: P[BlockStatement] =
    P(span("{" ~ annotations ~ (statement.rep(1) ~ annotations).? ~ "}"))
    .map({
      case ((post, None), span) => BlockStatement(List.empty, span, List.empty, post)
      case ((pre, Some((stmts, post))), span) => stmts.toList match {
        case head :: tl => BlockStatement(head.withSpecifications(pre ++ head.specifications) :: tl, span, List.empty, post)
        case Nil => ??? // This should be impossible since no statements would result in None
      }
    })
  
  def ifStatement[_: P]: P[IfStatement] =
    P(span(kw("if") ~ "(" ~ expression ~ ")" ~ statement ~ ("else" ~ statement).?)).map({
      case ((condition, body, els), span) => IfStatement(condition, body, els, span)
    })
  
  def whileStatement[_: P]: P[WhileStatement] =
    P(span(kw("while") ~ "(" ~ expression ~ ")" ~ statement)).map({
      case ((condition, body), span) => WhileStatement(condition, body, span)
    })

  def forStatement[_: P]: P[ForStatement] =
    P(span(kw("for") ~ "(" ~/ simpleStatement ~ ";" ~ expression ~ ";" ~ simpleStatement ~ ")" ~ statement)).map({
      case ((init, condition, next, body), span) => ForStatement(init, condition, next, body, span)
    })

  def returnStatement[_: P]: P[ReturnStatement] =
    P(span(kw("return") ~ expression.? ~ ";")).map({
      case (value, span) => ReturnStatement(value, span)
    })

  def assertStatement[_: P]: P[AssertStatement] =
    P(span(kw("assert") ~ "(" ~ expression ~ ")" ~ ";")).map({
      case (value, span) => AssertStatement(value, span)
    })
  
  def errorStatement[_: P]: P[ErrorStatement] =
    P(span(kw("error") ~ "(" ~ expression ~ ")" ~ ";")).map({
      case (value, span) => ErrorStatement(value, span)
    })

  def simpleStatement[_: P]: P[Statement] =
    P(variableStatement | expressionStatement)

  def variableStatement[_: P]: P[VariableStatement] =
    P(span(typeReference ~ identifier ~ ("=" ~ expression).?)).map({
      case ((varType, varName, value), span) => VariableStatement(varType, varName, value, span)
    })

  def expressionStatement[_: P]: P[Statement] = P(span(expression ~/ statementTail.?))
    .map({
      case ((expr, None), span) => ExpressionStatement(expr, span)
      case ((expr, Some(PostfixTail(op))), span) => UnaryOperationStatement(expr, op, span)
      case ((expr, Some(AssignmentTail(op, value))), span) => AssignmentStatement(expr, op, value, span)
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