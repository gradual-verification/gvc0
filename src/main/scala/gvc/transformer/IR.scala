package gvc.transformer

object IR {
  trait Node

  class Program(
     val methods: List[Method],
     val predicates: List[Predicate],
     val structs: List[StructDefinition]) extends Node

  sealed trait Method extends Node {
    val name: String;
    val returnType: Option[Type]
    val arguments: List[Var]
    val precondition: Expr[Relaxed]
    val postcondition: Expr[Relaxed]
  }

  class LibraryMethod(
     val name: String,
     val returnType: Option[Type],
     val arguments: List[Var],
     val precondition: Expr[Relaxed],
     val postcondition: Expr[Relaxed]) extends Method

  class MethodImplementation(
    val name: String,
    val returnType: Option[Type],
    val arguments: List[Var],
    val precondition: Expr[Relaxed],
    val postcondition: Expr[Relaxed],
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

  class Var(val varType: Type, val name: String)
    extends Value
      with FieldValue {
    def valueType: Option[Type] = Some(varType)
  }
  sealed trait FieldValue extends Expr[Relaxed]
  sealed trait FieldAccess extends FieldValue

  sealed trait ValueType extends Node {
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

  class Predicate(
     val name: String,
     val arguments: List[Var],
     val body: Option[Expr[Relaxed]]
   ) extends Node

  sealed trait Atomicity
  sealed trait Strict extends Atomicity
  sealed trait Relaxed extends Atomicity

  sealed abstract class Expr[A:Atomicity] extends Node{
    def valueType: Option[Type]
  }
  object Expr {
    class Arithmetic[A:Atomicity](val left: Expr[A], val right: Expr[A], val op: ArithmeticOp) extends Expr {
      def valueType = Some(Type.Int)
    }

    class Comparison[A:Atomicity](val left: Expr[A], val right: Expr[A], val op: ComparisonOp) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class Logical[A:Atomicity](val left: Expr[A], val right: Expr[A], val op: LogicalOp) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class ArrayAccess[A:Atomicity](val subject: Var, val index: Expr[A]) extends Expr {
      def valueType = subject.valueType match {
        case Some(Type.Array(memberType: Type)) => Some(memberType)
        case _ => None
      }
    }

    class ArrayFieldAccess[A:Atomicity](val subject: Var, val index: Expr[A], val field: StructField) extends Expr {
      def valueType = Some(field.valueType)
    }

    class Negation[A:Atomicity](val value: Expr[A]) extends Expr {
      def valueType = Some(Type.Int)
    }

    class Not[A:Atomicity](val value: Expr[A]) extends Expr {
      def valueType = Some(Type.Bool)
    }

    class Member[A:Atomicity](val subject: Var, val field: StructField) extends Expr {
      def valueType = Some(field.valueType)
    }

    class Deref[A:Atomicity](val subject: Var) extends Expr {
      def valueType = subject.valueType match {
        case Some(Type.Pointer(memberType)) => Some(memberType)
        case _ => None
      }
    }
  }

  sealed trait SpecExpr extends Expr[Relaxed]
  object SpecExpr {
    class Accessibility(val field: FieldAccess) extends SpecExpr {
      def valueType: Option[Type] = Some(Type.Bool)
    }
    class Predicate(val predicateName: String, val arguments: List[Expr[Relaxed]]) extends SpecExpr {
      def valueType: Option[Type] = Some(Type.Bool)
    }
    class Imprecision(val spec: Expr[Relaxed]) extends SpecExpr {
      def valueType: Option[Type] = Some(Type.Bool)
    }
    abstract class ReturnValue extends FieldValue

  }
  sealed trait ProgramExpr extends Expr[Strict]
  object ProgramExpr {
    class Alloc(val memberType: ValueType) extends ProgramExpr {
      def valueType = memberType match {
        case Type.StructValue(struct) => Some(Type.StructReference(struct.name, Some(struct)))
        case t: Type => Some(Type.Pointer(t))
      }
    }

    class AllocArray(val memberType: ValueType, val length: Value) extends ProgramExpr {
      def valueType = Some(Type.Array(memberType))
    }

    class Invoke(val methodName: String, val arguments: List[Value], val returnType: Option[Type]) extends ProgramExpr {
      def valueType = returnType
    }
  }

  sealed trait Value extends Expr[Strict]
  sealed trait Literal extends Value
  object Literal{
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
    class AssignVar(val subject: Var, val value: Expr[Strict]) extends SimpleOp
    class AssignMember(val subject: Var, val field: StructField, val value: Value) extends SimpleOp
    class AssignArray(val subject: Var, val index: Value, val value: Value) extends SimpleOp
    // arr[i].field needs to be encoded differently in Viper and C0 so make a special-case for it
    class AssignArrayMember(val subject: Var, val index: Value, val field: StructField, val value: Value) extends SimpleOp
    class AssignPtr(val subject: Var, val value: Value) extends SimpleOp
    class While(val condition: Value, val invariant: Expr[Relaxed], val body: Block) extends FlowOp
    class If(val condition: Value, val ifTrue: Block, val ifFalse: Block) extends FlowOp
    class Assert(val value: Value) extends SimpleOp
    class AssertSpec(val spec: Expr[Relaxed]) extends SimpleOp
    class Fold(val predicate: Predicate) extends SimpleOp
    class Unfold(val predicate: Predicate) extends SimpleOp
    class Error(val value: Value) extends SimpleOp
    class Return(val value: Option[Value]) extends SimpleOp
    class Noop(val value: Expr[Relaxed]) extends SimpleOp
  }


}
