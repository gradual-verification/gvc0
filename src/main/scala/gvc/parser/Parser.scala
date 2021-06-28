package gvc.parser
import fastparse.Parsed.Failure
import fastparse.Parsed.Success

class Parser(val annotation: Boolean = false) extends Definitions {
  import fastparse._

  def program[_: P]: P[List[AstDefinition]] =
    P(Start ~ definition.rep ~ End).map(defs => defs.toList)

  // Explicitly use start token to allow leading whitespace
  def expressionProgram[_: P]: P[AstExpression] = P(Start ~ expression ~ End)
  def statementProgram[_: P]: P[AstStatement] = P(Start ~ statement ~ End)
  def definitionProgram[_: P]: P[AstDefinition] = P(Start ~ definition ~ End)
}

object Parser {
  import fastparse.Parsed

  def parseExpr(src: String): Parsed[AstExpression] = {
    val parser = new Parser()
    fastparse.parse(src, parser.expressionProgram(_))
  }

  def parseStatement(src: String): Parsed[AstStatement] = {
    val parser = new Parser()
    fastparse.parse(src, parser.statementProgram(_))
  }

  def parseDef(src: String): Parsed[AstDefinition] = {
    val parser = new Parser()
    fastparse.parse(src, parser.definitionProgram(_))
  }

  def parseProgram(src: String): Parsed[List[AstDefinition]] = {
    val parser = new Parser()
    fastparse.parse(src, parser.program(_))
  }
}