package gvc.analyzer
import scala.collection.mutable.ArrayBuffer
import gvc.parser._

case class Error(
  node: Node,
  message: String,
)

class ErrorSink {
  private val errorList = new ArrayBuffer[Error]()
  def errors = errorList.toList

  def error(node: Node, message: String): Unit = {
    errorList += Error(node, message)
  }
}