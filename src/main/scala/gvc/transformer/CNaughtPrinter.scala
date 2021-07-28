package gvc.transformer

object CNaughtPrinter {
  def typeName(t: IR.ValueType): String = {
    t match {
      case IR.Type.Array(memberType) => typeName(memberType) + "[]"
      case IR.Type.Pointer(memberType) => typeName(memberType) + "*"
      case IR.Type.StructValue(struct) => "struct " + struct.name
      case IR.Type.StructReference(name, _) => "struct " + name + "*"
      case IR.Type.Int => "int"
      case IR.Type.Char => "char"
      case IR.Type.String => "string"
      case IR.Type.Bool => "bool"
    }
  }

  def printMethod(method: IR.MethodImplementation): String = {
    val printer = new Printer()
    printer.print(method, printMethod)
    printer.toString()
  }

  def printMethod(method: IR.MethodImplementation, printer: Printer): Unit = {
    // Return type
    printer.print(method.returnType.map(typeName).getOrElse("void"))
    printer.print(" ")
    printer.print(method.name)
    printer.print("(")
    printer.print(method.arguments.map(v => typeName(v.varType) + " " + v.name).mkString(", "))
    printer.println(")")
    printer.println("{")
    for (variable <- method.variables) {
      printer.printIndented(variable, (v: IR.Var, printer) => {
        printer.print(typeName(v.varType))
        printer.print(" ")
        printer.print(v.name)
        printer.println(";")
      })
    }

    for (op <- method.body.operations) {
      printer.printIndented(op, printOp)
    }
    printer.println("}")

    def printBlock(block: IR.Block): Unit = {
      printer.println("{")
      for (op <- block.operations) {
        printer.printIndented(op, printOp)
      }
      printer.println("}")
    }

    def printOp(op: IR.Op, printer: Printer): Unit = {
      op match {
        case assign: IR.Op.AssignVar => {
          printer.print(assign.subject.name)
          printer.print(" = ")
          printer.print(assign.value, printExpr)
          printer.println(";")
        }

        case member: IR.Op.AssignMember => {
          printer.print(member.subject.name)
          printer.print(".")
          printer.print(member.field.name)
          printer.print(" = ")
          printer.print(member.value, printValue)
        }

        case assign: IR.Op.AssignArray => {
          printer.print(assign.subject.name)
          printer.print("[")
          printer.print(assign.index, printValue)
          printer.print("] = ")
          printer.print(assign.value, printValue)
          printer.println(";")
        }

        case assign: IR.Op.AssignArrayMember => {
          printer.print(assign.subject.name)
          printer.print("[")
          printer.print(assign.index, printValue)
          printer.print("].")
          printer.print(assign.field.name)
          printer.print(" = ")
          printer.print(assign.value, printValue)
          printer.println(";")
        }

        case assign: IR.Op.AssignPtr => {
          printer.print("*(")
          printer.print(assign.subject.name)
          printer.print(") = ")
          printer.print(assign.value, printValue)
          printer.println(";")
        }

        case w: IR.Op.While => {
          printer.print("while (")
          printer.print(w.condition, printValue)
          printer.println(")")
          printBlock(w.body)
        }

        case iff: IR.Op.If => {
          printer.print("if (")
          printer.print(iff.condition, printValue)
          printer.println(")")
          printBlock(iff.ifTrue)
          if (!iff.ifFalse.operations.isEmpty) {
            printer.println("else")
            printBlock(iff.ifFalse)
          }
        }

        // Do not output assert specifications
        case _: IR.Op.AssertSpec => ()

        case assert: IR.Op.Assert => {
          printer.print("assert(");
          printer.print(assert.value, printValue)
          printer.println(");")
        }

        case error: IR.Op.Error => {
          printer.print("error(")
          printer.print(error.value, printValue)
          printer.println(");")
        }

        case ret: IR.Op.Return => {
          printer.print("return");
          ret.value.foreach { value =>
            printer.print(" ")
            printer.print(value, printValue)
          }
          printer.println(";")
        }

        case noop: IR.Op.Noop => {
          printer.print(noop.value, printExpr)
          printer.println(";")
        }
      }
    }

    def printValue(value: IR.Value, printer: Printer) = {
      value match {
        case variable: IR.Var => printer.print(variable.name)

        case str: IR.Literal.String => {
          printer.print("\"")
          printer.print(str.value
            .replace("\\", "\\\\")
            .replace("\n", "\\n")
            .replace("\r", "\\r")
            .replace("\t", "\\t")
            // TODO: Complete escape
          )
          printer.print("\"")
        }

        case int: IR.Literal.Int => printer.print(int.value.toString())
        case char: IR.Literal.Char => {
          printer.print("'")
          printer.print(char.value match {
            case '\\' => "\\\\"
            case '\n' => "\\n"
            case '\r' => "\\r"
            case '\t' => "\\t"
            case other => other.toString()
          })
          printer.print("'")
        }

        case bool: IR.Literal.Bool => printer.print(bool.value match {
          case true => "true"
          case false => "false"
        })

        case IR.Literal.Null => printer.print("NULL")
      }
    }

    def printExpr(expr: IR.Expr, printer: Printer) = {
      expr match {
        case value: IR.Value => printer.print(value, printValue)
        case a: IR.Expr.Arithmetic => {
          printer.print(a.left, printValue)
          printer.print(" ")
          printer.print(a.op match {
            case IR.ArithmeticOp.Add => "+"
            case IR.ArithmeticOp.Subtract => "-"
            case IR.ArithmeticOp.Multiply => "*"
            case IR.ArithmeticOp.Divide => "/"
          })
          printer.print(" ")
          printer.print(a.right, printValue)
        }

        case c: IR.Expr.Comparison => {
          printer.print(c.left, printValue)
          printer.print(" ")
          printer.print(c.op match {
            case IR.ComparisonOp.Equal => "=="
            case IR.ComparisonOp.NotEqual => "!="
            case IR.ComparisonOp.LessThan => "<"
            case IR.ComparisonOp.LessThanEqual => "<="
            case IR.ComparisonOp.GreaterThan => ">"
            case IR.ComparisonOp.GreaterThanEqual => ">="
          })
          printer.print(" ")
          printer.print(c.right, printValue)
        }

        case l: IR.Expr.Logical => {
          printer.print(l.left, printValue)
          printer.print(" ")
          printer.print(l.op match {
            case IR.LogicalOp.And => "&&"
            case IR.LogicalOp.Or => "||"
          })
          printer.print(" ")
          printer.print(l.right, printValue)
        }

        case arr: IR.Expr.ArrayAccess => {
          printer.print(arr.subject.name)
          printer.print("[")
          printer.print(arr.index, printValue)
          printer.print("]")
        }

        case arrField: IR.Expr.ArrayFieldAccess => {
          printer.print(arrField.subject.name)
          printer.print("[")
          printer.print(arrField.index, printValue)
          printer.print("]")
        }

        case deref: IR.Expr.Deref => {
          printer.print("*")
          printer.print(deref.subject.name)
        }

        case negate: IR.Expr.Negation => {
          printer.print("-")
          printer.print(negate.value, printValue)
        }

        case not: IR.Expr.Not => {
          printer.print("!")
          printer.print(not.value, printValue)
        }

        case member: IR.Expr.Member => {
          printer.print(member.subject.name)
          printer.print("->")
          printer.print(member.field.name)
        }

        case alloc: IR.Expr.Alloc => {
          printer.print("alloc(")
          printer.print(typeName(alloc.memberType))
          printer.print(")")
        }

        case allocArray: IR.Expr.AllocArray => {
          printer.print("alloc_array(")
          printer.print(typeName(allocArray.memberType))
          printer.print(", ")
          printer.print(allocArray.length, printValue)
          printer.print(")")
        }

        case invoke: IR.Expr.Invoke => {
          printer.print(invoke.methodName)
          printer.print("(")
          var first = true
          for (arg <- invoke.arguments) {
            if (first) {
              first = false
            } else {
              printer.print(", ")
            }
            printer.print(arg, printValue)
          }
          printer.print(")")
        }
      }
    }
  }
}