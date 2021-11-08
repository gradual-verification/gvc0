package gvc.transformer

object IR {
  trait Node

  class Program(
     val methods: List[Method],
     val predicates: List[Predicate],
     val structs: List[StructDefinition]) extends Node

  sealed trait Method extends Node {
    val name: String
    val returnType: Option[Type]
    val arguments: List[Var]
    val precondition: SpecExpr
    val postcondition: SpecExpr
  }

  class LibraryMethod(
    val name: String,
    val returnType: Option[Type],
    val arguments: List[Var],
    val precondition: SpecExpr,
    val postcondition: SpecExpr,
  ) extends Method

  class MethodImplementation(
    val name: String,
    val returnType: Option[Type],
    val arguments: List[Var],
    val precondition: SpecExpr,
    val postcondition: SpecExpr,
    val variables: List[Var],
    val body: Block) extends Method

  class Block(val operations: List[Op]) extends Node

  // Make this a trait to hide some of the mutability necessary to create
  // circular links between field types and struct definitions
  trait StructDefinition extends Node {
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
   val valueType: Type) extends Node

  sealed trait ValueType extends Node {
    def name: String
  }

  sealed trait Type extends ValueType
  object Type {
    case class Array(memberType: ValueType) extends Type { def name: String = memberType.name + "[]" }
    case class Pointer(memberType: Type) extends Type { def name: String = memberType.name + "*" }
    case class StructReference(structName: String, definition: Option[StructDefinition]) extends Type { def name: String = "struct " + structName + "*" }
    case class StructValue(definition: StructDefinition) extends ValueType { def name: String = "struct " + definition.name }
    case object Int extends Type { val name = "int" }
    case object Char extends Type { val name = "char" }
    case object String extends Type { val name = "string" }
    case object Bool extends Type { val name = "bool" }
  }
  
  abstract sealed class Expr extends Node {
    def valueType: Option[Type]
  }

  sealed trait ProgramExpr extends Expr

  object Expr {
    trait LogicalExpr extends Expr{
      val left: Expr
      val right: Expr
      val op: LogicalOp
      def valueType: Option[Type.Bool.type] = Some(Type.Bool)
    }
    trait ComparisonExpr extends Expr{
      val left: Expr
      val right: Expr
      val op: ComparisonOp
      def valueType: Option[Type.Bool.type] = Some(Type.Bool)
    }
    trait ArithmeticExpr extends Expr{
      val left: Expr
      val right: Expr
      val op: ArithmeticOp
      def valueType: Option[Type.Int.type] = Some(Type.Int)
    }
    trait NegateExpr extends Expr{
      val value: Expr
      def valueType: Option[Type.Int.type] = Some(Type.Int)
    }
    trait NotExpr extends Expr{
      val value: Expr
      def valueType: Option[Type.Bool.type] = Some(Type.Bool)
    }
    trait CalledExpr extends Expr{
      val name: String
      val arguments: List[Expr]
    }
    trait ArrayExpr extends Expr{
      val subject: Var
      val index: Value
    }
  }

  sealed trait Value extends Expr with ProgramExpr with SpecExpr

  class Var(val varType: Type, val name: String)
    extends Value
    with SpecExpr
    with FieldValue {
    def valueType: Option[Type] = Some(varType)
  }

  sealed trait Literal extends Value
  object Literal {
    class String(val value: java.lang.String) extends Literal {
      def valueType: Option[Type.String.type] = Some(Type.String)
    }

    class Int(val value: Integer) extends Literal with SpecExpr {
      def valueType: Option[Type.Int.type] = Some(Type.Int)
    }

    class Char(val value: scala.Char) extends Literal with SpecExpr {
      def valueType: Option[Type.Char.type] = Some(Type.Char)
    }

    class Bool(val value: Boolean) extends Literal with SpecExpr {
      def valueType: Option[Type.Bool.type] = Some(Type.Bool)
    }

    object Null extends Literal with SpecExpr {
      def valueType: Option[Nothing] = None
    }
  }

  object ProgramExpr {
    class Arithmetic(val left: Value, val right: Value, val op: ArithmeticOp) extends ProgramExpr with Expr.ArithmeticExpr

    class Comparison(val left: Value, val right: Value, val op: ComparisonOp) extends ProgramExpr with Expr.ComparisonExpr

    class Logical(val left: Value, val right: Value, val op: LogicalOp) extends ProgramExpr with Expr.LogicalExpr

    class ArrayAccess(val subject: Var, val index: Value) extends ProgramExpr with Expr.ArrayExpr {
      def valueType: Option[Type] = subject.valueType match {
        case Some(Type.Array(memberType: IR.Type)) => Some(memberType)
        case _ => None
      }
    }

    class ArrayFieldAccess(val subject: Var, val index: Value, val field: StructField) extends ProgramExpr with Expr.ArrayExpr {
      def valueType: Option[Type] = Some(field.valueType)
    }

    class Deref(val subject: Var) extends ProgramExpr {
      def valueType: Option[Type] = subject.valueType match {
        case Some(Type.Pointer(memberType)) => Some(memberType)
        case _ => None
      }
    }

    class Negation(val value: Value) extends ProgramExpr with Expr.NegateExpr

    class Not(val value: Value) extends ProgramExpr with Expr.NotExpr

    class Member(val subject: Var, val field: StructField) extends ProgramExpr {
      def valueType: Option[Type] = Some(field.valueType)
    }
    abstract class ReturnValue extends FieldValue

    class Alloc(val memberType: ValueType) extends ProgramExpr {
      def valueType: Option[Type] = memberType match {
        case Type.StructValue(struct) => Some(Type.StructReference(struct.name, Some(struct)))
        case t: Type => Some(Type.Pointer(t))
      }
    }

    class AllocArray(val memberType: ValueType, val length: Value) extends ProgramExpr {
      def valueType: Option[Type.Array] = Some(Type.Array(memberType))
    }

    class Invoke(val name: String, val arguments: List[Value], val returnType: Option[Type]) extends ProgramExpr with Expr.CalledExpr {
      def valueType: Option[Type] = returnType
    }
  }

  sealed trait LogicalOp extends Op
  object LogicalOp {
    case object And extends LogicalOp
    case object Or extends LogicalOp
  }

  sealed trait ComparisonOp extends Op
  object ComparisonOp {
    case object Equal extends ComparisonOp
    case object NotEqual extends ComparisonOp
    case object LessThan extends ComparisonOp
    case object LessThanEqual extends ComparisonOp
    case object GreaterThan extends ComparisonOp
    case object GreaterThanEqual extends ComparisonOp
  }
  sealed trait ArithmeticOp extends Op
  object ArithmeticOp {
    case object Add extends ArithmeticOp
    case object Subtract extends ArithmeticOp
    case object Multiply extends ArithmeticOp
    case object Divide extends ArithmeticOp
  }

  sealed trait Op extends Node
  sealed trait SimpleOp extends Op
  sealed trait FlowOp extends Op

  object Op {
    class AssignVar(val subject: Var, val value: Expr) extends SimpleOp
    class AssignMember(val subject: Var, val field: StructField, val value: Value) extends SimpleOp
    class AssignArray(val subject: Var, val index: Value, val value: Value) extends SimpleOp
    // arr[i].field needs to be encoded differently in Viper and C0 so make a special-case for it
    class AssignArrayMember(val subject: Var, val index: Value, val field: StructField, val value: Value) extends SimpleOp
    class AssignPtr(val subject: Var, val value: Value) extends SimpleOp
    class While(val condition: Value, val invariant: SpecExpr, val body: Block) extends FlowOp
    class If(val condition: Value, val ifTrue: Block, val ifFalse: Block) extends FlowOp
    class Assert(val value: Value) extends SimpleOp
    class AssertSpecExpr(val spec: SpecExpr) extends SimpleOp
    class Fold(val predicate: SpecExpr.Predicate) extends SimpleOp
    class Unfold(val predicate: SpecExpr.Predicate) extends SimpleOp
    class Error(val value: Value) extends SimpleOp
    class Return(val value: Option[Value]) extends SimpleOp
    class Noop(val value: Expr) extends SimpleOp
  }

  sealed trait SpecExpr extends Expr
  sealed trait FieldValue extends SpecExpr
  sealed trait FieldAccess extends FieldValue

  class Predicate(
    val name: String,
    val arguments: List[Var],
    val body: Option[SpecExpr]
  ) extends Node

  object SpecExpr {
    class ReturnValue(val returnValueType: Type) extends FieldValue {
      def valueType: Option[Type] = Some(returnValueType)
    }
    class Member(val parent: FieldValue, val field: StructField) extends FieldAccess {
      def valueType: Option[Type] = Some(field.valueType)
    }
    class Dereference(val pointer: FieldValue, val pointerType: Type) extends FieldAccess{
      def valueType: Option[Type] = Some(pointerType)
    }
    class Imprecision(val spec: SpecExpr) extends SpecExpr {
      override def valueType: Option[Type] = Some(Type.Bool)
    }
    class Logical(val left: SpecExpr, val right: SpecExpr, val op: LogicalOp) extends SpecExpr with Expr.LogicalExpr
    class Comparison(val left: SpecExpr, val right: SpecExpr, val op: ComparisonOp) extends SpecExpr with Expr.ComparisonExpr

    //TODO: can a conditional expression have different types in each branch?
    class Conditional(val condition: SpecExpr, val ifTrue: SpecExpr, val ifFalse: SpecExpr) extends SpecExpr {
      def valueType: Option[Type] = ifTrue.valueType match  {
        case Some(valueTypeTrue) => Some(valueTypeTrue)
        case None => ifFalse.valueType match {
            case Some(valueTypeFalse) => Some(valueTypeFalse)
            case None => None
          }

      }
    }
    class Arithmetic(val left: SpecExpr, val right: SpecExpr, val op: ArithmeticOp) extends SpecExpr with Expr.ArithmeticExpr
    class Negate(val value: SpecExpr) extends SpecExpr with Expr.NegateExpr
    class Not(val value: SpecExpr) extends SpecExpr with Expr.NotExpr
    class Accessibility(val field: FieldAccess) extends SpecExpr {
      override def valueType: Option[Type] = Some(Type.Bool)
    }
    class Predicate(val name: String, val arguments: List[SpecExpr]) extends SpecExpr with Expr.CalledExpr {
      override def valueType: Option[Type] = Some(Type.Bool)
    }
  }
}
