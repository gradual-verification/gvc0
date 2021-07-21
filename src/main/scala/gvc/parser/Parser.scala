package gvc.parser

class Parser(val state: ParserState) extends Definitions {
  import fastparse._

  def this(source: String) {
    this(new ParserState(source))
  }

  def program[_: P]: P[List[Definition]] =
    P(Start ~ definition.rep ~ End).map(defs => defs.toList)

  // Explicitly use start token to allow leading whitespace
  def expressionProgram[_: P]: P[Expression] = P(Start ~ expression ~ End)
  def statementProgram[_: P]: P[Statement] = P(Start ~ statement ~ End)
  def definitionProgram[_: P]: P[Definition] = P(Start ~ definition ~ End)
  def specificationProgram[_: P]: P[List[Specification]] = P(Start ~ annotations ~ End)
}

object Parser {
  import fastparse.Parsed

  def parseExpr(src: String): Parsed[Expression] = {
    val parser = new Parser(src)
    fastparse.parse(src, parser.expressionProgram(_))
  }

  def parseStatement(src: String): Parsed[Statement] = {
    val parser = new Parser(src)
    fastparse.parse(src, parser.statementProgram(_))
  }

  def parseDef(src: String): Parsed[Definition] = {
    val parser = new Parser(src)
    fastparse.parse(src, parser.definitionProgram(_))
  }

  def parseSpec(src: String): Parsed[List[Specification]] = {
    val parser = new Parser(src)
    fastparse.parse(src, parser.specificationProgram(_))
  }

  def parseProgram(src: String): Parsed[List[Definition]] = {
    val parser = new Parser(src)
    fastparse.parse(src, parser.program(_))
  }
}