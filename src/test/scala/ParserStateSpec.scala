import org.scalatest.funsuite._
import gvc._
import fastparse.Parsed.{Success, Failure}

class ParserStateSpec extends AnyFunSuite {
  test("start position") {
    val state = new ParserState("this is a test")
    val LineColPosition(line, col) = state.position(0)
    assert(line ==  1)
    assert(col == 1)
  }

  test("middle of single line") {
    val state = new ParserState("this is a test")
    val LineColPosition(line, col) = state.position(5)
    assert(line == 1)
    assert(col == 6)
  }

  test("at new line char") {
    val state = new ParserState("test\n")
    val LineColPosition(line, col) = state.position(4)
    assert(line == 1)
    assert(col == 5)
  }

  test("start of next line") {
    val state = new ParserState("test\nabc\n")
    val LineColPosition(line, col) = state.position(5)
    assert(line == 2)
    assert(col == 1)
  }

  test("end of second line") {
    val state = new ParserState("test\nabc\n")
    val LineColPosition(line, col) = state.position(8)
    assert(line == 2)
    assert(col == 4)
  }

  test("last line") {
    val state = new ParserState("test\nabc")
    val LineColPosition(line, col) = state.position(5)
    assert(line == 2)
    assert(col == 1)
  }
}