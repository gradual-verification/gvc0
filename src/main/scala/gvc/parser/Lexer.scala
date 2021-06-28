package gvc.parser
import fastparse._

trait Lexer extends Whitespace {
  def identifier[_: P] =
    P(CharIn("A-Za-z_") ~~ CharIn("A-Za-z0-9_").repX)

  def decimalNumber[_: P] =
    P("0" | (CharIn("1-9") ~~ CharIn("0-9").repX))

  def hexNumber[_: P] =
    P("0" ~~ CharIn("xX") ~~ CharIn("0-9a-fA-F").repX(1))

  def string[_: P] = P("\"" ~~ stringChar.repX ~~ "\"")

  def character[_: P] = P("'" ~~ charChar.repX ~~ "'")

  def library[_: P] = P("<" ~~ libraryChar.repX ~~ ">")

  def stringChar[_: P] = P(normalChar | escape)

  def charChar[_: P] = P(normalChar | escape | "\"" | "\\0")

  def normalChar[_: P] =
    P(CharPred(c => c != '"' && c != '\\' && !c.isControl))

  def libraryChar[_: P] =
    P(CharPred(c => c != '>' && !c.isControl))
  
  // <esc> ::= ::= \n | \t | \v | \b | \r | \f | \a | \\ | \' | \"
  def escape[_: P] = P("\\" ~~ CharIn("ntvbrfa\\\"'"))

  // <unop> ::= ! | ~ | - | *
  def prefixOperator[_: P] = P(CharIn("!~\\-*"))

    // <postop> ::= -- | ++
  def postfixOperator[_: P] = P(StringIn("--", "++"))

  def binaryOperator[_: P] =
    P(StringIn("*", "/", "%", "+", "-", "<<", ">>",
               "<", "<=", ">=", ">", "==", "!=",
               "&", "^", "|", "&&", "||"));

  def assignmentOperator[_: P] =
    P(StringIn("=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=",
                "&=", "^=", "|="))
}