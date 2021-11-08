package gvc.transformer

object CNaughtPrinter {
  private var printSpecifications: Boolean = false
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

  def printProgram(program: IR.Program): String = {
    val printer = new Printer()

    var first = true

    // TODO: Print structs and method headers so that everything can compile
    for (method <- program.methods) {
      method match {
        case impl: IR.MethodImplementation => {
          if (first) first = false
          else printer.println()

          printer.print(impl, printMethod)
        }
        case _ => ()
      }
    }

    printer.toString()
  }


  def printMethod(method: IR.MethodImplementation, printSpecs: Boolean): String = {
    val printer = new Printer()
    this.printSpecifications = printSpecs
    printer.print(method, printMethod)
    printer.toString()
  }

  private def printMethod(method: IR.MethodImplementation, printer: Printer): Unit = {
    // Return type
    printer.print(method.returnType.map(typeName).getOrElse("void"))
    printer.print(" ")
    printer.print(method.name)
    printer.print("(")
    printer.print(method.arguments.map(v => typeName(v.varType) + " " + v.name).mkString(", "))
    printer.println(")")
    printer.println("{")

    if(this.printSpecifications){
      printer.printIndented(method.precondition, (pre: IR.SpecExpr, printer) => {
        printer.print("/@ requires ")
        printer.print(pre, printExpr)
        printer.println("; @*/")
      })
      printer.printIndented(method.postcondition, (pre: IR.SpecExpr, printer) => {
        printer.print("/@ ensures ")
        printer.print(pre, printExpr)
        printer.println("; @*/")
      })
    }

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
          printer.println(";")
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

        case assertSpec: IR.Op.AssertSpecExpr => {
          if(this.printSpecifications){
            printer.print("assert(")
            printer.print(assertSpec.spec, printExpr)
            printer.println(");")
          }
        }
        case fold: IR.Op.Fold => {
          if (this.printSpecifications) {
            printer.print("fold(")
            printer.print(fold.predicate, printExpr)
            printer.println(");")
          }
        }
        case unfold: IR.Op.Unfold => {
          if(this.printSpecifications) {
            printer.print("fold(")
            printer.print(unfold.predicate, printExpr)
            printer.println(");")
          }
        }

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

    def printExpr(expr: IR.Expr, printer: Printer): Unit = {
      expr match {
        case impr: IR.SpecExpr.Imprecision => {
          printer.print("? && ")
          printer.print(impr.spec, printExpr)
        }
        case value: IR.Value => printer.print(value, printValue)
        case a: IR.Expr.ArithmeticExpr => {
          printer.print(a.left, printExpr)
          printer.print(" ")
          printer.print(a.op match {
            case IR.ArithmeticOp.Add => "+"
            case IR.ArithmeticOp.Subtract => "-"
            case IR.ArithmeticOp.Multiply => "*"
            case IR.ArithmeticOp.Divide => "/"
          })
          printer.print(" ")
          printer.print(a.right, printExpr)
        }

        case c: IR.Expr.ComparisonExpr => {
          printer.print(c.left, printExpr)
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
          printer.print(c.right, printExpr)
        }

        case l: IR.Expr.LogicalExpr => {
          printer.print(l.left, printExpr)
          printer.print(" ")
          printer.print(l.op match {
            case IR.LogicalOp.And => "&&"
            case IR.LogicalOp.Or => "||"
          })
          printer.print(" ")
          printer.print(l.right, printExpr)
        }

        case arr: IR.Expr.ArrayExpr => {
          printer.print(arr.subject.name)
          printer.print("[")
          printer.print(arr.index, printValue)
          printer.print("]")
        }

        case deref: IR.ProgramExpr.Deref => {
          printer.print("*")
          printer.print(deref.subject.name)
        }

        case negate: IR.Expr.NegateExpr => {
          printer.print("-")
          printer.print(negate.value, printExpr)
        }

        case not: IR.Expr.NotExpr => {
          printer.print("!")
          printer.print(not.value, printExpr)
        }

        case member: IR.ProgramExpr.Member => {
          printer.print(member.subject.name)
          printer.print("->")
          printer.print(member.field.name)
        }

        case alloc: IR.ProgramExpr.Alloc => {
          printer.print("alloc(")
          printer.print(typeName(alloc.memberType))
          printer.print(")")
        }

        case allocArray: IR.ProgramExpr.AllocArray => {
          printer.print("alloc_array(")
          printer.print(typeName(allocArray.memberType))
          printer.print(", ")
          printer.print(allocArray.length, printValue)
          printer.print(")")
        }

        case called: IR.Expr.CalledExpr => {
          printer.print(called.name)
          printer.print("(")
          var first = true
          for (arg <- called.arguments) {
            if (first) {
              first = false
            } else {
              printer.print(", ")
            }
            printer.print(arg, printExpr)
          }
          printer.print(")")
        }
        case acc: IR.SpecExpr.Predicate => {

        }
      }
    }
  }
}