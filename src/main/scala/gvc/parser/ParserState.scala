package gvc.parser

import scala.collection.mutable.ArrayBuffer
import scala.collection.Searching._

class ParserState(
  val lines: Array[Int],
  val singleLine: Boolean = false
) {
  def this(source: String) {
    this(ParserState.splitLines(source), false)
  }

  def position(index: Int): LineColPosition = {
    val lineIndex = lines.search(index) match {
      case Found(i) => i
      case InsertionPoint(i) => i
    }

    val column = lineIndex match {
      case 0 => index + 1
      case _ => index - lines(lineIndex - 1)
    }

    LineColPosition(lineIndex + 1, column)
  }

  def inSingleLine(): ParserState = new ParserState(lines, true)
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