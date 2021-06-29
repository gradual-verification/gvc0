import org.scalatest.funsuite._
import gvc.parser.{ParserState, SourcePosition}
import fastparse.Parsed.{Success, Failure}
import gvc.parser.MultiLineAnnotation
import gvc.parser.SingleLineAnnotation

class ParserStateSpec extends AnyFunSuite {
  test("start position") {
    val state = new ParserState("this is a test")
    val SourcePosition(line, col, i) = state.position(0)
    assert(line ==  1)
    assert(col == 1)
    assert(i == 0)
  }

  test("middle of single line") {
    val state = new ParserState("this is a test")
    val SourcePosition(line, col, i) = state.position(5)
    assert(line == 1)
    assert(col == 6)
    assert(i == 5)
  }

  test("at new line char") {
    val state = new ParserState("test\n")
    val SourcePosition(line, col, i) = state.position(4)
    assert(line == 1)
    assert(col == 5)
    assert(i == 4)
  }

  test("start of next line") {
    val state = new ParserState("test\nabc\n")
    val SourcePosition(line, col, i) = state.position(5)
    assert(line == 2)
    assert(col == 1)
    assert(i == 5)
  }

  test("end of second line") {
    val state = new ParserState("test\nabc\n")
    val SourcePosition(line, col, i) = state.position(8)
    assert(line == 2)
    assert(col == 4)
    assert(i == 8)
  }

  test("last line") {
    val state = new ParserState("test\nabc")
    val SourcePosition(line, col, i) = state.position(5)
    assert(line == 2)
    assert(col == 1)
    assert(i == 5)
  }

  test("annotation sub-parser") {
    val state = new ParserState("test")
    val child = state.inAnnotation()
    assert(child.mode == MultiLineAnnotation)
  }

  test("single line annotation sub-parser") {
    val state = new ParserState("test")
    val sub = state.inSingleLineAnnotation()
    assert(sub.mode == SingleLineAnnotation)
  }
}