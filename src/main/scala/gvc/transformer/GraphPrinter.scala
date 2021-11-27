package gvc.transformer
import gvc.transformer.IRGraph._

object GraphPrinter {
  private object Precedence {
    val Unary = 1
    val Multiply = 2
    val Add = 3
    val Inequality = 4
    val Equality = 5
    val And = 6
    val Or = 7
    val Conditional = 8
    val Top = 9
  }

  def print(program: Program): String = {
    val p = new Printer()

    def printList[T](values: Seq[T])(action: T => Unit): Unit = {
      var first = true
      for (value <- values) {
        if (first) first = false
        else p.print(", ")
        action(value)
      }
    }

    def printStructHeader(struct: Struct): Unit = {
      p.print("struct ")
      p.print(struct.name)
    }

    def printStruct(struct: Struct): Unit = {
      printStructHeader(struct)
      p.println()
      p.println("{")
      p.withIndent {
        for (field <- struct.fields) {
          printType(field.valueType)
          p.print(" ")
          p.print(field.name)
          p.println(";")
        }
      }
      p.println("};")
    }

    def printType(t: Type): Unit = p.print(t.name)

    def printMethodHeader(method: Method): Unit = {
      method.returnType match {
        case None => p.print("void")
        case Some(ret) => printType(ret)
      }

      p.print(" ")
      p.print(method.name)
      p.print("(")

      var first = true
      printList(method.parameters) { param =>
        printType(param.valueType)
        p.print(" ")
        p.print(param.name)
      }

      p.print(")")
    }

    def printMethod(method: Method): Unit = {
      printMethodHeader(method)
      p.println()

      method.precondition.foreach {pre =>
        p.withIndent {
          p.print("//@requires ")
          printExpr(pre)
          p.println(";")
        }
      }

      method.postcondition.foreach { post =>
        p.withIndent {
          p.print("//@ensures ")
          printExpr(post)
          p.println(";")
        }
      }

      p.println("{")
      p.withIndent {
        for (decl <- method.variables) {
          printVar(decl)
        }

        printBlock(method.entry)
      }
      p.println("}")
    }

    def printVar(decl: Var): Unit = {
      printType(decl.valueType)
      p.print(" ")
      p.print(decl.name)
      p.print(" = ")
      printExpr(decl.valueType.default)
      p.println(";")
    }

    def printBlock(block: Block): Unit = {
      block match {
        case basic: BasicBlock => {
          for (op <- basic.ops) printOp(op)
        }

        case iff: IfBlock => {
          p.print("if (")
          printExpr(iff.condition)
          p.println(")")
          p.println("{")
          p.withIndent { printBlock(iff.ifTrue) }
          p.println("}")
          if (iff.ifFalse.ops.nonEmpty || iff.ifFalse.next.isDefined) {
            p.println("else")
            p.println("{")
            p.withIndent { printBlock(iff.ifFalse) }
            p.println("}")
          }
        }

        case loop: WhileBlock => {
          p.print("while (")
          printExpr(loop.condition)
          p.println(")")

          loop.invariant.foreach { invariant =>
            p.withIndent {
              p.print("//@loop_invariant ")
              printExpr(invariant)
              p.println(";")
            }
          }

          p.println("{")
          p.withIndent { printBlock(loop.body) }
          p.println("}")
        }
      }

      block.next match {
        case None => ()
        case Some(next) => printBlock(next)
      }
    }

    def printOp(op: Op): Unit = op match {
      case invoke: Invoke => {
        invoke.target.foreach { target =>
          printExpr(target)
          p.print(" = ")
        }

        p.print(invoke.method.name)
        p.print("(")

        printList(invoke.arguments) { arg =>
          printExpr(arg)
        }

        p.println(");")
      }
      case alloc: AllocValue => {
        printExpr(alloc.target)
        p.print(" = alloc(")
        printType(alloc.valueType)
        p.println(");")
      }

      case alloc: AllocStruct => {
        printExpr(alloc.target)
        p.print(" = alloc(struct ")
        p.print(alloc.struct.name)
        p.println(");")
      }

      case assign: Assign => {
        printExpr(assign.target)
        p.print(" = ")
        printExpr(assign.value)
        p.println(";")
      }

      case assign: AssignMember => {
        printExpr(assign.target)
        p.print("->")
        p.print(assign.field.name)
        p.print(" = ")
        printExpr(assign.value)
        p.println(";")
      }
      case assign: AssignPointer => {
        p.print("*(")
        printExpr(assign.target)
        p.print(") = ")
        printExpr(assign.value)
        p.println(";")
      }

      case assert: Assert => assert.method match {
        case AssertMethod.Specification => {
          p.print("//@assert ")
          printExpr(assert.value)
          p.println(";")
        }
        case AssertMethod.Imperative => {
          p.print("assert(")
          printExpr(assert.value)
          p.println(");")
        }
      }

      case fold: Fold => {
        p.print("fold ")
        printExpr(fold.instance)
        p.println(";")
      }

      case unfold: Unfold => {
        p.print("unfold ")
        printExpr(unfold.instance)
        p.println(";")
      }

      case error: IRGraph.Error => {
        p.print("error(")
        printExpr(error.value)
        p.println(");")
      }

      case ret: Return => ret.value match {
        case None => p.println("return;")
        case Some(value) => {
          p.print("return ")
          printExpr(value)
          p.println(";")
        }
      }
    }

    def wrapExpr(currentPrecedence: scala.Int, exprPrecedence: scala.Int)(action: => Unit): Unit = {
      if (currentPrecedence < exprPrecedence) {
        p.print("(")
        action
        p.print(")")
      } else {
        action
      }
    }

    def printExpr(expr: Expression, precedence: scala.Int = Precedence.Top): Unit = expr match {
      case v: Var => p.print(v.name)
      case m: Member => {
        printExpr(m.instance)
        p.print("->")
        p.print(m.field.name)
      }
      case acc: Accessibility => {
        p.print("acc(")
        printExpr(acc.member)
        p.print(")")
      }
      case pred: PredicateInstance => {
        p.print(pred.predicate.name)
        p.print("(")
        printList(pred.arguments) { arg => printExpr(arg) }
        p.print(")")
      }

      case res: Result => p.print("\\result")
      case imp: Imprecise => imp.precise match {
        case None => p.print("?")
        case Some(precise) => wrapExpr(precedence, Precedence.And) {
          p.print("? && ")
          printExpr(precise, Precedence.And)
        }
      }
      case int: Int => p.print(int.value.toString())
      case char: Char => {
        p.print("'")
        p.print(char.value match {
          case '\\' => "\\\\"
          case '\n' => "\\n"
          case '\r' => "\\r"
          case '\t' => "\\t"
          case other => other.toString()
        })
        p.print("'")
      }
      case bool: Bool => p.print(if (bool.value) "true" else "false")
      case _: Null => p.print("NULL")

      case cond: Conditional => wrapExpr(precedence, Precedence.Conditional) {
        printExpr(cond.condition, Precedence.Conditional)
        p.print(" ? ")
        printExpr(cond.ifTrue, Precedence.Conditional)
        p.print(" : ")
        printExpr(cond.ifFalse, Precedence.Conditional)
      }

      case binary: Binary => {
        val (sep, opPrecedence) = binary.operator match {
          case BinaryOp.Add => (" + ", Precedence.Add)
          case BinaryOp.Subtract => (" - ", Precedence.Add)
          case BinaryOp.Divide => (" / ", Precedence.Multiply)
          case BinaryOp.Multiply => (" * ", Precedence.Multiply)
          case BinaryOp.And => (" && ", Precedence.And)
          case BinaryOp.Or => (" || ", Precedence.Or)
          case BinaryOp.Equal => (" == ", Precedence.Equality)
          case BinaryOp.NotEqual => (" != ", Precedence.Equality)
          case BinaryOp.Less => (" < ", Precedence.Inequality)
          case BinaryOp.LessOrEqual => (" <= ", Precedence.Inequality)
          case BinaryOp.Greater => (" > ", Precedence.Inequality)
          case BinaryOp.GreaterOrEqual => (" >= ", Precedence.Inequality)
        }

        wrapExpr(precedence, opPrecedence) {
          printExpr(binary.left, opPrecedence)
          p.print(sep)
          printExpr(binary.right, opPrecedence)
        }
      }

      case unary: Unary => wrapExpr(precedence, Precedence.Unary) {
        p.print(unary.operator match {
          case UnaryOp.Dereference => "*"
          case UnaryOp.Not => "!"
          case UnaryOp.Negate => "-"
        })
        printExpr(unary.operand, Precedence.Unary)
      }
    }

    var empty = true
    def printSeparator() = {
      if (!empty) {
        empty = true
        p.println()
      }
    }

    for (struct <- program.structs) {
      printStructHeader(struct)
      p.println(";")
      empty = false
    }

    printSeparator()

    for (struct <- program.structs) {
      printStruct(struct)
      p.println()
    }
    
    for(method <- program.methods) {
      printMethodHeader(method)
      p.println(";")
      empty = false
    }

    printSeparator()

    var first = true
    for (method <- program.methods) {
      if (first) first = false
      else p.println()
      printMethod(method)
    }

    p.toString()
  }

  private class Printer {
    var indentLevel = 0
    var startedLine = false
    val indentValue = "  "
    private val builder = new StringBuilder()

    private def startLine(): Unit = {
      if (!startedLine) {
        startedLine = true
        for (_ <- 0 until indentLevel) {
          builder ++= indentValue
        }
      }
    }

    def withIndent[T](action: => Unit): Unit = {
      indentLevel += 1
      action
      indentLevel -= 1
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
}