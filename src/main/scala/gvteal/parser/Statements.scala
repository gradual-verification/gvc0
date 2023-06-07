package gvc.parser
import fastparse._
import scala.collection.mutable.ListBuffer

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

  private sealed trait BlockPiece
  private case class BlockStatementPiece(s: Statement) extends BlockPiece
  private case class BlockAnnotationPiece(s: Seq[Specification]) extends BlockPiece

  private def blockPiece[_: P]: P[BlockPiece] =
    P(concreteStatement.map(BlockStatementPiece(_)) | annotation.map(BlockAnnotationPiece(_)))

  def blockStatement[_: P]: P[BlockStatement] =
    P(span("{" ~ blockPiece.rep ~ "}"))
    .map({
      case (pieces, span) =>
        var specs = List.empty[Specification]
        val stmts = ListBuffer[Statement]()
        for (piece <- pieces) {
          piece match {
            case BlockAnnotationPiece(s) => specs = specs ++ s
            case BlockStatementPiece(s) => {
              specs match {
                case Nil => stmts += s
                case _ => {
                  stmts += s.withSpecifications(specs ++ s.specifications)
                  specs = Nil
                }
              }
            }
          }
        }

        BlockStatement(stmts.toList, span, Nil, specs)
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

  def expressionStatement[_: P]: P[Statement] = P(span(expression ~/ assignmentTail.?))
    .map({
      case ((expr, None), span) => ExpressionStatement(expr, span)
      case ((expr, Some((op, value))), span) => AssignmentStatement(expr, op, value, span)
    })

  def assignmentTail[_: P]: P[(AssignOperator.Value, Expression)] = P(assignmentOperator.! ~ expression)
    .map({
      case (assignOp, value) => (parseAssignOperator(assignOp), value)
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