package gvc.transformer

object IR {
  class Program(
    val methods: List[Method],
    val structs: List[StructDefinition]
  )

  sealed trait Method {
    val name: String;
    val returnType: Option[Type]
    val arguments: List[Var]
    val precondition: Spec
    val postcondition: Spec
  }

  class LibraryMethod(
    val name: String,
    val returnType: Option[Type],
    val arguments: List[Var],
    val precondition: Spec,
    val postcondition: Spec,
  ) extends Method

  class MethodImplementation(
    val name: String,
    val returnType: Option[Type],
    val arguments: List[Var],
    val precondition: Spec,
    val postcondition: Spec,
    val variables: List[Var],
    val body: Block
  ) extends Method

  // Make this a trait to hide some of the mutability necessary to create
  // circular links between field types and struct definitions
  trait StructDefinition {
    val name: String
    def fields: List[StructField]

    // Could make use of hash table, but we do need an ordered list for determinate C0 output
    def field(name: String): StructField = fields.find(_.name == name) match {
      case None => throw new TransformerException("Invalid struct field")
      case Some(value) => value
    }
  }

  class StructField(
    val name: String,
    val struct: StructDefinition,
    val valueType: Type,
  )

  sealed trait ValueType {
    def name: String
  }

  sealed trait Type extends ValueType

  object Type {
    case class Array(memberType: ValueType) extends Type { def name = memberType.name + "[]" }
    case class Pointer(memberType: Type) extends Type { def name = memberType.name + "*" }
    case class StructReference(structName: String, definition: Option[StructDefinition]) extends Type { def name = "struct " + structName + "*" }
    case class StructValue(definition: StructDefinition) extends ValueType { def name = "struct " + definition.name }
    case object Int extends Type { val name = "int" }
    case object Char extends Type { val name = "char" }
    case object String extends Type { val name = "string" }
    case object Bool extends Type { val name = "bool" }
  }
  
  sealed trait Expr {
    def valueType: Option[Type]
  }

  sealed trait Value extends Expr

  class Var(val varType: Type, val name: String)
    extends Value
    with Spec
    with FieldValue {
    def valueType: Option[Type] = Some(varType)
  }

  sealed trait Literal extends Value
  object Literal {
    class String(val value: java.lang.String) extends Literal {
      def valueType = Some(Type.String)
    }

    class Int(val value: Integer) extends Literal with Spec {
      def valueType = Some(Type.Int)
    }

    class Char(val value: scala.Char) extends Literal {
      def valueType = Some(Type.Char)
    }

    class Bool(val value: Boolean) extends Literal with Spec {
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
        case Some(Type.Array(memberType: IR.Type)) => Some(memberType)
        case _ => None
      }
    }

    class ArrayFieldAccess(val subject: Var, val index: Value, val field: StructField) extends Expr {
      def valueType = Some(field.valueType)
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

    class Member(val subject: Var, val field: StructField) extends Expr {
      def valueType = Some(field.valueType)
    }

    class Alloc(val memberType: ValueType) extends Expr {
      def valueType = memberType match {
        case Type.StructValue(struct) => Some(Type.StructReference(struct.name, Some(struct)))
        case t: IR.Type => Some(Type.Pointer(t))
      }
    }

    class AllocArray(val memberType: ValueType, val length: Value) extends Expr {
      def valueType = Some(Type.Array(memberType))
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
    class AssignMember(val subject: Var, val field: StructField, val value: Value) extends SimpleOp
    class AssignArray(val subject: Var, val index: Value, val value: Value) extends SimpleOp
    // arr[i].field needs to be encoded differently in Viper and C0 so make a special-case for it
    class AssignArrayMember(val subject: Var, val index: Value, val field: StructField, val value: Value) extends SimpleOp
    class AssignPtr(val subject: Var, val value: Value) extends SimpleOp
    class While(val condition: Value, val invariant: Spec, val body: Block) extends FlowOp
    class If(val condition: Value, val ifTrue: Block, val ifFalse: Block) extends FlowOp
    class Assert(val value: Value) extends SimpleOp
    class AssertSpec(val spec: Spec) extends SimpleOp
    class Error(val value: Value) extends SimpleOp
    class Return(val value: Option[Value]) extends SimpleOp
    class Noop(val value: Expr) extends SimpleOp
  }

  class Block(val operations: List[Op])

  sealed trait Spec

  object Spec {
    val True = new Literal.Bool(true)
    class ReturnValue extends Spec with FieldValue
    class Imprecision extends Spec
    class Comparison(val left: Spec, val right: Spec, val op: ComparisonOp) extends Spec
    class Conjunction(val left: Spec, val right: Spec) extends Spec
    class Conditional(val condition: Spec, val ifTrue: Spec, val ifFalse: Spec) extends Spec
    class Accessibility(val field: FieldAccess) extends Spec
  }

  sealed trait FieldValue
  sealed trait FieldAccess extends FieldValue
  object FieldAccess {
    class Member(val parent: FieldValue, val field: StructField) extends FieldAccess
    class Dereference(val pointer: FieldValue) extends FieldAccess
  }
}