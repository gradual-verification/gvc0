package gvteal.parser
import fastparse._

trait Whitespace {
  val state: ParserState

  // Whitespace is a regular space, horizontal and vertical tab,
  // newline, formfeed and comments
  // Comments can be single-line (#) or multi-line (""" ... """)
  // Python does not support nested multi-line comments!
  implicit val whitespace = { implicit ctx: ParsingRun[_] => space }

  def space[_: P] = P(state.mode match {
    case DefaultMode => normalWhitespace.repX
    case MultiLineAnnotation => multiLineAnnotationWhitespace.repX
    case SingleLineAnnotation => singleLineAnnotationWhitespace.repX
  })

  def normalWhitespace[_: P] =
    P(normalWhitespaceChar | singleLineComment | multiLineComment)
  def singleLineAnnotationWhitespace[_: P] =
    P(singleLineAnnotationWhitespaceChar | singleLineComment | multiLineComment)
  def multiLineAnnotationWhitespace[_: P] =
    P(multiLineAnnotationWhitespaceChar | singleLineComment | multiLineComment)

  def normalWhitespaceChar[_: P] =
    P(CharIn(" \t\u000b\f\r\n"))
  def singleLineAnnotationWhitespaceChar[_: P] =
    P(CharIn(" \t\u000b\f\r@"))
  def multiLineAnnotationWhitespaceChar[_: P] =
    P(CharIn(" \t\u000b\f\r\n") | (!"@*/" ~~ "@"))

  def singleLineComment[_: P] = P("#" ~~ !"@" ~~/ (!"\n" ~~ AnyChar).repX ~~ &("\n"))

  def multiLineComment[_: P]: P[Unit] = P("\"\"\"" ~~ !"@" ~~/ (multiLineComment | multiLineCommentChar).repX ~~ "\"\"\"")

  def multiLineCommentChar[_: P]: P[Unit] = P(state.mode match {
    case SingleLineAnnotation => !("\"\"\"" | "\n") ~~ AnyChar
    case _ => !"\"\"\"" ~~ AnyChar
  })
}