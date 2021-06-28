package gvc.parser
import fastparse._

trait Whitespace {
  val annotation: Boolean

  // Whitespace is a regular space, horizontal and vertical tab,
  // newline, formfeed and comments
  // Comments can be single-line (//) or multi-line (/* ... */)
  // Multi-line comments can be nested (/* ... /* ... */ ... */)
  implicit val whitespace = { implicit ctx: ParsingRun[_] =>
    var index = ctx.index
    val input = ctx.input

    def standard() = {
      while (input.isReachable(index) && (input(index) match {
        case '/' if
          input.isReachable(index + 1) &&
          input(index + 1) == '/' &&
          input.isReachable(index + 2) &&
          input(index + 2) != '@' =>
        {
          index += 2
          lineComment()
          true
        }

        case '/' if
          input.isReachable(index + 1) &&
          input(index + 1) == '*' &&
          input.isReachable(index + 2) &&
          input(index + 2) != '@' =>
        {
          index += 2
          multiLineComment()
          true
        }

        case ' ' | '\t' | '\13' | '\n' | '\r' => {
          index += 1
          true
        }

        case _ => false
      }))()
    }

    def lineComment() = {
      while (input.isReachable(index) &&
        (input(index) match {
          case '\r' | '\n' => {
            index += 1
            false
          }
          case _ => {
            index += 1
            true
          }
        })
      )()
    }

    def multiLineComment(): Unit = {
      while (input.isReachable(index) &&
        (input(index) match {
          case '*' if input.isReachable(index + 1) && input(index + 1) == '/' => {
            index += 2
            false
          }

          case '/' if input.isReachable(index + 1) && input(index + 1) == '*' => {
            index += 2
            multiLineComment()
            true
          }

          case _ => {
            index += 1
            true
          }
        })
      )()
    }

    standard()
    ctx.freshSuccessUnit(index = index)
  }
}