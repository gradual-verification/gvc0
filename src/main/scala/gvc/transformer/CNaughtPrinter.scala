package gvc.transformer
import scala.collection.mutable
import gvc.transformer.IR.Var
import gvc.transformer.IR.Literal.Bool
import gvc.transformer.IR.Expr.Arithmetic
import gvc.transformer.IR.Expr.Comparison
import gvc.transformer.IR.Expr.Logical
import gvc.transformer.IR.Expr.ArrayAccess
import gvc.transformer.IR.Expr.ArrayFieldAccess
import gvc.transformer.IR.Expr.Deref
import gvc.transformer.IR.Expr.Negation
import gvc.transformer.IR.Expr.Not
import gvc.transformer.IR.Expr.Member
import gvc.transformer.IR.Expr.Alloc
import gvc.transformer.IR.Expr.AllocArray
import gvc.transformer.IR.Expr.Invoke
import gvc.transformer.IR.ArithmeticOp.Add
import gvc.transformer.IR.ArithmeticOp.Subtract
import gvc.transformer.IR.ArithmeticOp.Multiply
import gvc.transformer.IR.ArithmeticOp.Divide
import gvc.transformer.IR.ComparisonOp.Equal
import gvc.transformer.IR.ComparisonOp.NotEqual
import gvc.transformer.IR.ComparisonOp.LessThan
import gvc.transformer.IR.ComparisonOp.LessThanEqual
import gvc.transformer.IR.ComparisonOp.GreaterThan
import gvc.transformer.IR.ComparisonOp.GreaterThanEqual

object CNaughtPrinter {
  def typeName(t: IR.Type): String = {
    t match {
      case IR.Type.Array(memberType) => typeName(memberType) + "[]"
      case IR.Type.Pointer(memberType) => typeName(memberType) + "*"
      case IR.Type.Struct(name) => "struct " + name
      case IR.Type.Int => "int"
      case IR.Type.Char => "char"
      case IR.Type.String => "string"
      case IR.Type.Bool => "bool"
    }
  }

  def nameVariables(variables: Seq[IR.Var]): Map[IR.Var, String] = {
    val used = mutable.Set[String]()
    variables.map({ variable =>
      val baseName = variable.nameHint.getOrElse("_")
      var num = 1
      while (used.contains(baseName + num))
        num += 1
      
      val name = baseName + num
      used += name
      (variable, name)
    }).toMap
  }

  def printMethod(method: IR.MethodImplementation): String = {
    val printer = new Printer()
    printer.print(method, printMethod)
    printer.toString()
  }

  def printMethod(method: IR.MethodImplementation, printer: Printer): Unit = {
    def varNames = nameVariables(method.arguments ++ method.variables)
    // Return type
    printer.print(method.returnType.map(typeName).getOrElse("void"))
    printer.print(" ")
    printer.print(method.name)
    printer.print("(")
    printer.print(method.arguments.map(v => typeName(v.varType) + " " + varNames(v)).mkString(", "))
    printer.println(")")
    printer.println("{")
    for (variable <- method.variables) {
      printer.printIndented(variable, (v: IR.Var, printer) => {
        printer.print(typeName(v.varType))
        printer.print(" ")
        printer.print(varNames(v))
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
          printer.print(varNames(assign.subject))
          printer.print(" = ")
          printer.print(assign.value, printExpr)
          printer.println(";")
        }

        case member: IR.Op.AssignMember => {
          printer.print(varNames(member.subject))
          printer.print(".")
          printer.print(member.fieldName)
          printer.print(" = ")
          printer.print(member.value, printValue)
        }

        case assign: IR.Op.AssignArray => {
          printer.print(varNames(assign.subject))
          printer.print("[")
          printer.print(assign.index, printValue)
          printer.print("] = ")
          printer.print(assign.value, printValue)
          printer.println(";")
        }

        case assign: IR.Op.AssignArrayMember => {
          printer.print(varNames(assign.subject))
          printer.print("[")
          printer.print(assign.index, printValue)
          printer.print("].")
          printer.print(assign.fieldName)
          printer.print(" = ")
          printer.print(assign.value, printValue)
          printer.println(";")
        }

        case assign: IR.Op.AssignPtr => {
          printer.print("*(")
          printer.print(varNames(assign.subject))
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

        // Do not output asserts
        case _: IR.Op.Assert => ()

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
        case variable: IR.Var => printer.print(varNames(variable))

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

        case bool: Bool => printer.print(bool.value match {
          case true => "true"
          case false => "false"
        })

        case IR.Literal.Null => printer.print("NULL")
      }
    }

    def printExpr(expr: IR.Expr, printer: Printer) = {
      expr match {
        case value: IR.Value => printer.print(value, printValue)
        case a: Arithmetic => {
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

        case c: Comparison => {
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

        case l: Logical => {
          printer.print(l.left, printValue)
          printer.print(" ")
          printer.print(l.op match {
            case IR.LogicalOp.And => "&&"
            case IR.LogicalOp.Or => "||"
          })
          printer.print(" ")
          printer.print(l.right, printValue)
        }

        case arr: ArrayAccess => {
          printer.print(varNames(arr.subject))
          printer.print("[")
          printer.print(arr.index, printValue)
          printer.print("]")
        }

        case arrField: ArrayFieldAccess => {
          printer.print(varNames(arrField.subject))
          printer.print("[")
          printer.print(arrField.index, printValue)
          printer.print("]")
        }

        case deref: Deref => {
          printer.print("*")
          printer.print(varNames(deref.subject))
        }

        case negate: Negation => {
          printer.print("-")
          printer.print(negate.value, printValue)
        }

        case not: Not => {
          printer.print("!")
          printer.print(not.value, printValue)
        }

        case member: Member => {
          printer.print(varNames(member.subject))
          printer.print("->")
          printer.print(member.fieldName)
        }

        case alloc: Alloc => {
          printer.print("alloc(")
          printer.print(typeName(alloc.memberType))
          printer.print(")")
        }

        case allocArray: AllocArray => {
          printer.print("alloc_array(")
          printer.print(typeName(allocArray.memberType))
          printer.print(", ")
          printer.print(allocArray.length, printValue)
          printer.print(")")
        }

        case invoke: Invoke => {
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