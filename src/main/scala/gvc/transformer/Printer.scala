package gvc.transformer

class Printer {
  var indentLevel = 0
  var startedLine = false
  val indentValue = "  "
  private val builder = new StringBuilder()

  type PrintAction[T] = (T, Printer) => Unit

  private def startLine(): Unit = {
    if (!startedLine) {
      startedLine = true
      for (_ <- 0 until indentLevel) {
        builder ++= indentValue
      }
    }
  }

  def printIndented[T](value: T, action: PrintAction[T]): Unit = {
    indentLevel += 1
    action(value, this)
    indentLevel -= 1
  }

  def print[T](value: T, action: PrintAction[T]): Unit = {
    action(value, this)
  }

  def print(value: String): Unit = {
    startLine()
    builder ++= value
  }

  def println(value: String): Unit = {
    startLine()
    builder ++= value
    builder += '\n'
    startedLine = false
  }

  def println(): Unit = {
    builder += '\n'
    startedLine = false
  }

  override def toString(): String = builder.toString()
}