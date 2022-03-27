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

  def print(program: Program, includeSpecs: Boolean): scala.Predef.String = {
    val p = new Printer()

    def printList[T](values: Seq[T])(action: T => Unit): Unit = {
      var first = true
      for (value <- values) {
        if (first) first = false
        else p.print(", ")
        action(value)
      }
    }

    def printDependency(dependency: Dependency): Unit = {
      p.print("#use ")
      if (dependency.isLibrary) {
        p.print("<" + dependency.path + ">")
      } else {
        p.print("\"" + dependency.path + "\"")
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

    def printPredicateHeader(predicate: Predicate): Unit = {
      p.print("//@predicate ")
      p.print(predicate.name)
      p.print("(")
      printList(predicate.parameters) { param =>
        printType(param.varType)
        p.print(" ")
        p.print(param.name)
      }
      p.print(")")
    }

    def printPredicate(predicate: Predicate): Unit = {
      printPredicateHeader(predicate)
      p.print(" = ")
      printExpr(predicate.expression)
      p.println(";")
    }

    def printMethodHeader(method: Method): Unit = {
      method.returnType match {
        case None      => p.print("void")
        case Some(ret) => printType(ret)
      }

      p.print(" ")
      p.print(method.name)
      p.print("(")

      var first = true
      printList(method.parameters) { param =>
        printType(param.varType)
        p.print(" ")
        p.print(param.name)
      }

      p.print(")")
    }

    def printMethod(method: Method): Unit = {
      printMethodHeader(method)
      p.println()

      if (includeSpecs) {
        method.precondition.foreach { pre =>
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
      }
      p.println("{")
      p.withIndent {
        method.variables.foreach(printVar)
        method.body.foreach(printOp)
      }
      p.println("}")
    }

    def printVar(v: Var): Unit = {
      p.print(v.varType.name)
      p.print(" ")
      p.print(v.name)
      v.varType match {
        case _: ArrayType | _: ReferenceArrayType => ()
        case varType => {
          p.print(" = ")
          printExpr(varType.default)
        }
      }
      p.println(";")
    }

    def printBlock(block: Block): Unit = {
      p.println("{")
      p.withIndent(block.foreach(printOp))
      p.println("}")
    }

    def printOp(op: Op): Unit = op match {
      case invoke: Invoke => {
        invoke.target.foreach { target =>
          printExpr(target)
          p.print(" = ")
        }

        p.print(invoke.callee.name)
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

      case alloc: AllocArray => {
        printExpr(alloc.target)
        p.print(" = alloc_array(")
        printType(alloc.valueType)
        p.print(", ")
        printExpr(alloc.length)
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
        assign.member match {
          case member: FieldMember => {
            printExpr(member.root)
            p.print("->")
            p.print(member.field.name)
          }
          case member: DereferenceMember => {
            p.print("*")
            printExpr(member.root, Precedence.Unary)
          }
          case member: ArrayMember => {
            printExpr(member.root)
            p.print("[")
            printExpr(member.index)
            p.print("]")
          }
        }

        p.print(" = ")
        printExpr(assign.value)
        p.println(";")
      }

      case assert: Assert =>
        assert.kind match {
          case AssertKind.Specification =>
            if (includeSpecs) {
              p.print("//@assert ")
              printExpr(assert.value)
              p.println(";")
            }
          case AssertKind.Imperative => {
            p.print("assert(")
            printExpr(assert.value)
            p.println(");")
          }
        }

      case fold: Fold =>
        if (includeSpecs) {
          p.print("//@fold ")
          printExpr(fold.instance)
          p.println(";")
        }

      case unfold: Unfold =>
        if (includeSpecs) {
          p.print("//@unfold ")
          printExpr(unfold.instance)
          p.println(";")
        }

      case error: IRGraph.Error => {
        p.print("error(")
        printExpr(error.value)
        p.println(");")
      }

      case ret: Return => {
        p.print("return")
        ret.value.foreach { value =>
          p.print(" ")
          printExpr(value)
        }
        p.println(";")
      }

      case iff: If => {
        p.print("if (")
        printExpr(iff.condition)
        p.println(")")
        printBlock(iff.ifTrue)

        if (!iff.ifFalse.isEmpty) {
          p.println("else")
          printBlock(iff.ifFalse)
        }
      }

      case w: While => {
        p.print("while (")
        printExpr(w.condition)
        p.println(")")
        if (includeSpecs) {
          p.withIndent {
            p.print("//@loop_invariant ")
            printExpr(w.invariant)
            p.println(";")
          }
        }
        printBlock(w.body)
      }
    }

    def wrapExpr(currentPrecedence: scala.Int, exprPrecedence: scala.Int)(
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

    def printExpr(
        expr: Expression,
        precedence: scala.Int = Precedence.Top
    ): Unit = expr match {
      case v: Var => p.print(v.name)
      case m: FieldMember => {
        printExpr(m.root)
        p.print("->")
        p.print(m.field.name)
      }
      case deref: DereferenceMember =>
        wrapExpr(precedence, Precedence.Unary) {
          p.print("*")
          printExpr(deref.root, Precedence.Unary)
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
      case arr: ArrayMember => {
        printExpr(arr.root)
        p.print("[")
        printExpr(arr.index)
        p.print("]")
      }
      case res: Result => p.print("\\result")
      case imp: Imprecise =>
        imp.precise match {
          case None => p.print("?")
          case Some(precise) =>
            wrapExpr(precedence, Precedence.And) {
              p.print("? && ")
              printExpr(precise, Precedence.And)
            }
        }
      case int: Int => p.print(int.value.toString())
      case str: String =>
        p.print("\"")
        p.print(str.value)
        p.print("\"")
      case char: Char => {
        p.print("'")
        p.print(char.value match {
          case '\\'  => "\\\\"
          case '\n'  => "\\n"
          case '\r'  => "\\r"
          case '\t'  => "\\t"
          case other => other.toString()
        })
        p.print("'")
      }
      case bool: Bool => p.print(if (bool.value) "true" else "false")
      case _: Null    => p.print("NULL")

      case cond: Conditional =>
        wrapExpr(precedence, Precedence.Conditional) {
          printExpr(cond.condition, Precedence.Conditional)
          p.print(" ? ")
          printExpr(cond.ifTrue, Precedence.Conditional)
          p.print(" : ")
          printExpr(cond.ifFalse, Precedence.Conditional)
        }

      case binary: Binary => {
        val (sep, opPrecedence) = binary.operator match {
          case BinaryOp.Add            => (" + ", Precedence.Add)
          case BinaryOp.Subtract       => (" - ", Precedence.Add)
          case BinaryOp.Divide         => (" / ", Precedence.Multiply)
          case BinaryOp.Multiply       => (" * ", Precedence.Multiply)
          case BinaryOp.And            => (" && ", Precedence.And)
          case BinaryOp.Or             => (" || ", Precedence.Or)
          case BinaryOp.Equal          => (" == ", Precedence.Equality)
          case BinaryOp.NotEqual       => (" != ", Precedence.Equality)
          case BinaryOp.Less           => (" < ", Precedence.Inequality)
          case BinaryOp.LessOrEqual    => (" <= ", Precedence.Inequality)
          case BinaryOp.Greater        => (" > ", Precedence.Inequality)
          case BinaryOp.GreaterOrEqual => (" >= ", Precedence.Inequality)
        }

        wrapExpr(precedence, opPrecedence) {
          printExpr(binary.left, opPrecedence)
          p.print(sep)
          printExpr(binary.right, opPrecedence)
        }
      }

      case unary: Unary =>
        wrapExpr(precedence, Precedence.Unary) {
          p.print(unary.operator match {
            case UnaryOp.Not    => "!"
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

    for (method <- program.methods.filter(!_.maskedLibrary)) {
      printMethodHeader(method)
      p.println(";")
      empty = false
    }

    printSeparator()

    var first = true
    for (method <- program.methods.filter(!_.maskedLibrary)) {
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

    def print(value: scala.Predef.String): Unit = {
      startLine()
      builder ++= value
    }

    def println(value: scala.Predef.String): Unit = {
      startLine()
      builder ++= value
      builder += '\n'
      startedLine = false
    }

    def println(): Unit = {
      builder += '\n'
      startedLine = false
    }

    override def toString(): scala.Predef.String = builder.toString()
  }
}
