package gvc

import scala.collection.mutable.ArrayBuffer
import scala.collection.Searching._

class ParserState(source: String) {
  val lines = splitLines()

  def splitLines(): Array[Int] = {
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
}