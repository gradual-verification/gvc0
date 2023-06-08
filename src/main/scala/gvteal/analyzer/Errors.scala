package gvteal.analyzer
import scala.collection.mutable.ArrayBuffer
import gvteal.parser._

case class Error(
  node: Node,
  message: String,
) {
  override def toString(): String = {
    val loc = node match {
      case null => ""
      case expr => expr.span.start.line + ":" + expr.span.start.column + " - "
    }

    loc + message
  }
}

class ErrorSink {
  private val errorList = new ArrayBuffer[Error]()
  def errors = errorList.toList

  def error(node: Node, message: String): Unit = {
    errorList += Error(node, message)
  }

  def error(resolved: ResolvedNode, message: String): Unit = {
    errorList += Error(resolved.parsed, message)
  }

  def programError(message: String): Unit = {
    errorList += Error(null, message)
  }
}