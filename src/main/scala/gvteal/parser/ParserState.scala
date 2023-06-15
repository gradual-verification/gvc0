package gvteal.parser

import scala.collection.mutable.ArrayBuffer
import scala.collection.Searching._

sealed trait ParserMode
object DefaultMode extends ParserMode
object SingleLineAnnotation extends ParserMode
object MultiLineAnnotation extends ParserMode

class ParserState(
  val lines: Array[Int],
  val mode: ParserMode = DefaultMode
) {
  def this(source: String) {
    this(ParserState.splitLines(source))
  }

  def position(index: Int): SourcePosition = {
    val lineIndex = lines.search(index) match {
      case Found(i) => i
      case InsertionPoint(i) => i
    }

    val column = lineIndex match {
      case 0 => index + 1
      case _ => index - lines(lineIndex - 1)
    }

    SourcePosition(lineIndex + 1, column, index)
  }

  def inAnnotation(): ParserState = {
    println("Switching to inAnnotation() mode")
    new ParserState(
    lines = lines,
    mode = MultiLineAnnotation
    )
  }

def inSingleLineAnnotation(): ParserState = {
  println("Switching to SingleLineAnnotation mode")
  new ParserState(
    lines = lines,
    mode = SingleLineAnnotation
  )
}
}

object ParserState {
  private def splitLines(source: String): Array[Int] = {
    var positions = new ArrayBuffer[Int]()
    var i = 0

    while(source.indexOf('\n', i) match {
      case -1 => {
        positions += source.length()
        false
      }
      case pos => {
        positions += pos
        i = pos + 1
        true
      }
    })()

    positions.toArray
  }
}