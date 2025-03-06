package gvc.transformer

object IRPrinter {
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

  private def printExpr(
      p: Printer,
      expr: IR.Expression,
      precedence: Int = Precedence.Top
  ): Unit = expr match {
    case v: IR.Var => p.print(v.name)
    case m: IR.FieldMember => {
      printExpr(p, m.root)
      p.print("->")
      p.print(m.field.name)
    }
    case deref: IR.DereferenceMember =>
      wrapExpr(p, precedence, Precedence.Unary) {
        p.print("*")
        printExpr(p, deref.root, Precedence.Unary)
      }
    case acc: IR.Accessibility => {
      p.print("acc(")
      printExpr(p, acc.member)
      p.print(")")
    }
    case pred: IR.PredicateInstance => {
      p.print(pred.predicate.name)
      p.print("(")
      printList(p, pred.arguments) { arg => printExpr(p, arg) }
      p.print(")")
    }

    case unfolding: IR.Unfolding => {
      p.print("unfolding ")
      printExpr(unfolding.instance)
      p.print(" in")
      printExpr(unfolding.expr)
    }

    case arr: IR.ArrayMember => {
      printExpr(p, arr.root)
      p.print("[")
      printExpr(p, arr.index)
      p.print("]")
    }
    case res: IR.Result => p.print("\\result")
    case imp: IR.Imprecise =>
      imp.precise match {
        case None => p.print("?")
        case Some(precise) =>
          wrapExpr(p, precedence, Precedence.And) {
            p.print("? && ")
            printExpr(p, precise, Precedence.And)
          }
      }
    case int: IR.IntLit => p.print(int.value.toString())
    case str: IR.StringLit =>
      p.print("\"")
      p.print(str.value)
      p.print("\"")
    case char: IR.CharLit => {
      p.print("'")
      p.print(char.value match {
        case '\\'  => "\\\\"
        case '\n'  => "\\n"
        case '\r'  => "\\r"
        case '\t'  => "\\t"
        case '\u0000' => "\\0"
        case other => other.toString()
      })
      p.print("'")
    }
    case bool: IR.BoolLit => p.print(if (bool.value) "true" else "false")
    case _: IR.NullLit    => p.print("NULL")

    case cond: IR.Conditional =>
      wrapExpr(p, precedence, Precedence.Conditional) {
        printExpr(p, cond.condition, Precedence.Conditional)
        p.print(" ? ")
        printExpr(p, cond.ifTrue, Precedence.Conditional)
        p.print(" : ")
        printExpr(p, cond.ifFalse, Precedence.Conditional)
      }

    case binary: IR.Binary => {
      val (sep, opPrecedence) = binary.operator match {
        case IR.BinaryOp.Add            => (" + ", Precedence.Add)
        case IR.BinaryOp.Subtract       => (" - ", Precedence.Add)
        case IR.BinaryOp.Divide         => (" / ", Precedence.Multiply)
        case IR.BinaryOp.Multiply       => (" * ", Precedence.Multiply)
        case IR.BinaryOp.And            => (" && ", Precedence.And)
        case IR.BinaryOp.Or             => (" || ", Precedence.Or)
        case IR.BinaryOp.Equal          => (" == ", Precedence.Equality)
        case IR.BinaryOp.NotEqual       => (" != ", Precedence.Equality)
        case IR.BinaryOp.Less           => (" < ", Precedence.Inequality)
        case IR.BinaryOp.LessOrEqual    => (" <= ", Precedence.Inequality)
        case IR.BinaryOp.Greater        => (" > ", Precedence.Inequality)
        case IR.BinaryOp.GreaterOrEqual => (" >= ", Precedence.Inequality)
      }

      wrapExpr(p, precedence, opPrecedence) {
        printExpr(p, binary.left, opPrecedence)
        p.print(sep)
        printExpr(p, binary.right, opPrecedence)
      }
    }

    case unary: IR.Unary =>
      wrapExpr(p, precedence, Precedence.Unary) {
        p.print(unary.operator match {
          case IR.UnaryOp.Not    => "!"
          case IR.UnaryOp.Negate => "-"
        })
        printExpr(p, unary.operand, Precedence.Unary)
      }
  }

  def printList[T](p: Printer, values: Seq[T])(action: T => Unit): Unit = {
    var first = true
    for (value <- values) {
      if (first) first = false
      else p.print(", ")
      action(value)
    }
  }

  def wrapExpr(p: Printer, currentPrecedence: Int, exprPrecedence: Int)(
        action: => Unit
  ): Unit = {
    if (currentPrecedence < exprPrecedence) {
      p.print("(")
      action
      p.print(")")
    } else {
      action
    }
  }


  def print(program: IR.Program, includeSpecs: Boolean): String = {
    val p = new Printer()

    def printDependency(dependency: IR.Dependency): Unit = {
      p.print("#use ")
      if (dependency.isLibrary) {
        p.print("<" + dependency.path + ">")
      } else {
        p.print("\"" + dependency.path + "\"")
      }
    }
    def printStructHeader(struct: IR.Struct): Unit = {
      p.print("struct ")
      p.print(struct.name)
    }

    def printStruct(struct: IR.Struct): Unit = {
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

    def printType(t: IR.Type): Unit = p.print(t.name)

    def printPredicateHeader(predicate: IR.Predicate): Unit = {
      p.print("//@predicate ")
      p.print(predicate.name)
      p.print("(")
      printList(p, predicate.parameters) { param =>
        printType(param.varType)
        p.print(" ")
        p.print(param.name)
      }
      p.print(")")
    }

    def printPredicate(predicate: IR.Predicate): Unit = {
      printPredicateHeader(predicate)
      p.print(" = ")
      printExpr(p, predicate.expression)
      p.println(";")
    }

    def printMethodHeader(method: IR.Method): Unit = {
      method.returnType match {
        case None      => p.print("void")
        case Some(ret) => printType(ret)
      }

      p.print(" ")
      p.print(method.name)
      p.print("(")

      var first = true
      printList(p, method.parameters) { param =>
        printType(param.varType)
        p.print(" ")
        p.print(param.name)
      }

      p.print(")")
    }

    def printMethod(method: IR.Method): Unit = {
      printMethodHeader(method)
      p.println()

      if (includeSpecs) {
        method.precondition.foreach { pre =>
          p.withIndent {
            p.print("//@requires ")
            printExpr(p, pre)
            p.println(";")
          }
        }

        method.postcondition.foreach { post =>
          p.withIndent {
            p.print("//@ensures ")
            printExpr(p, post)
            p.println(";")
          }
        }
      }
      p.println("{")
      p.withIndent {
        method.variables.foreach(printVar)
        method.body.foreach(printOp)
      }
      p.println("}")
    }

    def printVar(v: IR.Var): Unit = {
      p.print(v.varType.name)
      p.print(" ")
      p.print(v.name)
      v.varType match {
        case _: IR.ArrayType | _: IR.ReferenceArrayType => ()
        case varType => {
          p.print(" = ")
          printExpr(p, varType.default)
        }
      }
      p.println(";")
    }

    def printBlock(block: IR.Block): Unit = {
      p.println("{")
      p.withIndent(block.foreach(printOp))
      p.println("}")
    }

    def printOp(op: IR.Op): Unit = op match {
      case invoke: IR.Invoke => {
        invoke.target.foreach { target =>
          printExpr(p, target)
          p.print(" = ")
        }

        p.print(invoke.callee.name)
        p.print("(")

        printList(p, invoke.arguments) { arg =>
          printExpr(p, arg)
        }

        p.println(");")
      }
      case alloc: IR.AllocValue => {
        printExpr(p, alloc.target)
        p.print(" = alloc(")
        printType(alloc.valueType)
        p.println(");")
      }

      case alloc: IR.AllocArray => {
        printExpr(p, alloc.target)
        p.print(" = alloc_array(")
        printType(alloc.valueType)
        p.print(", ")
        printExpr(p, alloc.length)
        p.println(");")
      }

      case alloc: IR.AllocStruct => {
        printExpr(p, alloc.target)
        p.print(" = alloc(struct ")
        p.print(alloc.struct.name)
        p.println(");")
      }

      case assign: IR.Assign => {
        printExpr(p, assign.target)
        p.print(" = ")
        printExpr(p, assign.value)
        p.println(";")
      }

      case assign: IR.AssignMember => {
        assign.member match {
          case member: IR.FieldMember => {
            printExpr(p, member.root)
            p.print("->")
            p.print(member.field.name)
          }
          case member: IR.DereferenceMember => {
            p.print("*")
            printExpr(p, member.root, Precedence.Unary)
          }
          case member: IR.ArrayMember => {
            printExpr(p, member.root)
            p.print("[")
            printExpr(p, member.index)
            p.print("]")
          }
        }

        p.print(" = ")
        printExpr(p, assign.value)
        p.println(";")
      }

      case assert: IR.Assert =>
        assert.kind match {
          case IR.AssertKind.Specification =>
            if (includeSpecs) {
              p.print("//@assert ")
              printExpr(p, assert.value)
              p.println(";")
            }
          case IR.AssertKind.Imperative => {
            p.print("assert(")
            printExpr(p, assert.value)
            p.println(");")
          }
        }

      case fold: IR.Fold =>
        if (includeSpecs) {
          p.print("//@fold ")
          printExpr(p, fold.instance)
          p.println(";")
        }

      case unfold: IR.Unfold =>
        if (includeSpecs) {
          p.print("//@unfold ")
          printExpr(p, unfold.instance)
          p.println(";")
        }

      case error: IR.Error => {
        p.print("error(")
        printExpr(p, error.value)
        p.println(");")
      }

      case ret: IR.Return => {
        p.print("return")
        ret.value.foreach { value =>
          p.print(" ")
          printExpr(p, value)
        }
        p.println(";")
      }

      case iff: IR.If => {
        p.print("if (")
        printExpr(p, iff.condition)
        p.println(")")
        printBlock(iff.ifTrue)

        if (!iff.ifFalse.isEmpty) {
          p.println("else")
          printBlock(iff.ifFalse)
        }
      }

      case w: IR.While => {
        p.print("while (")
        printExpr(p, w.condition)
        p.println(")")
        if (includeSpecs) {
          p.withIndent {
            p.print("//@loop_invariant ")
            printExpr(p, w.invariant)
            p.println(";")
          }
        }
        printBlock(w.body)
      }
    }


    var empty = true
    def printSeparator() = {
      if (!empty) {
        empty = true
        p.println()
      }
    }

    for (dep <- program.dependencies) {
      printDependency(dep)
      p.println()
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

    if (includeSpecs) {
      for (predicate <- program.predicates) {
        printPredicateHeader(predicate)
        p.println(";")
        empty = false
      }

      printSeparator()

      for (predicate <- program.predicates) {
        printPredicate(predicate)
        empty = false
      }
    }

    printSeparator()

    for (method <- program.methods) {
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

  def print(expr: IR.Expression) = {
    val p = new Printer()
    printExpr(p, expr)
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
