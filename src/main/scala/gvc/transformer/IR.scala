package gvc.transformer

object IR {
  class Method(val name: String, val returnType: Option[Type], val arguments: List[Var])

  class MethodImplementation(
    name: String,
    returnType: Option[Type],
    arguments: List[Var],
    val variables: List[Var],
    val body: Block
  ) extends Method(name, returnType, arguments)

  sealed trait Type {
    def name: String
  }

  object Type {
    case class Array(memberType: Type) extends Type { def name = memberType.name + "[]" }
    case class Pointer(memberType: Type) extends Type { def name = memberType.name + "*" }
    case class Struct(val name: String) extends Type
    case object Int extends Type { val name = "int" }
    case object Char extends Type { val name = "char" }
    case object String extends Type { val name = "string" }
    case object Bool extends Type { val name = "bool" }
  }
  
  sealed trait Expr {
    def valueType: Option[Type]
  }

  sealed trait Value extends Expr

  class Var(val varType: Type, val nameHint: Option[String] = None) extends Value {
    def valueType: Option[Type] = Some(varType)
  }

  sealed trait Literal extends Value
  object Literal {
    class String(val value: java.lang.String) extends Literal {
      def valueType = Some(Type.String)
    }

    class Int(val value: Integer) extends Literal {
      def valueType = Some(Type.Int)
    }

    class Char(val value: scala.Char) extends Literal {
      def valueType = Some(Type.Char)
    }

    class Bool(val value: Boolean) extends Literal {
      def valueType = Some(Type.Bool)
    }

    object Null extends Literal {
      def valueType = None
    }
  }
  
  sealed trait ArithmeticOp
  object ArithmeticOp {
    case object Add extends ArithmeticOp
    case object Subtract extends ArithmeticOp
    case object Multiply extends ArithmeticOp
    case object Divide extends ArithmeticOp
  }

  sealed trait ComparisonOp
  object ComparisonOp {
    case object Equal extends ComparisonOp
    case object NotEqual extends ComparisonOp
    case object LessThan extends ComparisonOp
    case object LessThanEqual extends ComparisonOp
    case object GreaterThan extends ComparisonOp
    case object GreaterThanEqual extends ComparisonOp
  }

  sealed trait LogicalOp
  object LogicalOp {
    case object And extends LogicalOp
    case object Or extends LogicalOp
  }

  object Expr {
    class Arithmetic(val left: Value, val right: Value, val op: ArithmeticOp) extends Expr {
      def valueType = Some(Type.Int)
    }

    class Comparison(val left: Value, val right: Value, val op: ComparisonOp) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class Logical(val left: Value, val right: Value, val op: LogicalOp) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class ArrayAccess(val subject: Var, val index: Value) extends Expr {
      def valueType = subject.valueType match {
        case Some(Type.Array(memberType)) => Some(memberType)
        case _ => None
      }
    }

    class ArrayFieldAccess(val subject: Var, val index: Value, val fieldName: String, val fieldType: Type) extends Expr {
      def valueType = Some(fieldType)
    }

    class Deref(val subject: Var) extends Expr {
      def valueType = subject.valueType match {
        case Some(Type.Pointer(memberType)) => Some(memberType)
        case _ => None
      }
    }

    class Negation(val value: Value) extends Expr {
      def valueType = Some(Type.Int)
    }

    class Not(val value: Value) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class Member(val subject: Var, val fieldName: String, val fieldType: Type) extends Expr {
      def valueType = Some(fieldType)
    }

    class Alloc(val memberType: Type) extends Expr {
      def valueType = Some(Type.Pointer(memberType))
    }

    class AllocArray(val memberType: Type, val length: Value) extends Expr {
      def valueType = Some(Type.Pointer(memberType))
    }

    class Invoke(val methodName: String, val arguments: List[Value], val returnType: Option[Type]) extends Expr {
      def valueType = returnType
    }
  }

  sealed trait Op
  sealed trait SimpleOp extends Op
  sealed trait FlowOp extends Op

  object Op {
    class AssignVar(val subject: Var, val value: Expr) extends SimpleOp
    class AssignMember(val subject: Var, val fieldName: String, val value: Value) extends SimpleOp
    class AssignArray(val subject: Var, val index: Value, val value: Value) extends SimpleOp
    // arr[i].field needs to be encoded differently in Viper and C0 so make a special-case for it
    class AssignArrayMember(val subject: Var, val index: Value, val fieldName: String, val value: Value) extends SimpleOp
    class AssignPtr(val subject: Var, val value: Value) extends SimpleOp
    class While(val condition: Value, val body: Block) extends FlowOp
    class If(val condition: Value, val ifTrue: Block, val ifFalse: Block) extends FlowOp
    class Assert(val value: Value) extends SimpleOp
    class Error(val value: Value) extends SimpleOp
    class Return(val value: Option[Value]) extends SimpleOp
    class Noop(val value: Expr) extends SimpleOp
  }

  class Block(val operations: List[Op])
}