package gvc.transformer
import scala.collection.mutable

object IRGraph {
  class IRException(message: String) extends Exception(message)

  // Note that names of methods, vars, etc. are immutable, since they are also copied in their respective Maps

  class Program {
    private val _structs = mutable.Map[String, Struct]()
    private val _methods = mutable.Map[String, Method]()
    private val _predicates = mutable.Map[String, Predicate]()

    def addMethod(name: String, returnType: Option[Type]): Method = {
      val method = new Method(name, returnType)
      if (_methods.getOrElseUpdate(method.name, method) != method)
        throw new IRException(s"Method '${method.name}' already exists")
      method
    }

    def addPredicate(name: String): Predicate = {
      val predicate = new Predicate(name, new IRGraph.Bool(true))
      if (_predicates.getOrElseUpdate(predicate.name, predicate) != predicate)
        throw new IRException(s"Predicate '${predicate.name}' already exists")
      predicate
    }

    def structs: Seq[Struct] = _structs.values.toSeq.sortBy(_.name)
    def methods: Seq[Method] = _methods.values.toSeq.sortBy(_.name)
    def predicates: Seq[Predicate] = _predicates.values.toSeq.sortBy(_.name)

    // Structs can be used even if they are never declared
    def struct(name: String): Struct = _structs.getOrElseUpdate(name, new Struct(name))
    def method(name: String): Method = _methods.getOrElse(name, throw new IRException(s"Method '$name' not found"))
    def predicate(name: String): Predicate = _predicates.getOrElse(name, throw new IRException(s"Predicate '$name' not found"))
  }

  class Struct(val name: String) {
    private val _fields = mutable.ListBuffer[StructField]()

    def addField(name: String, valueType: Type): StructField = {
      val field = new StructField(this, Helpers.findAvailableName(_fields.map(_.name), name), valueType)
      _fields += field
      field
    }

    def fields: Seq[StructField] = _fields
  }

  class StructField(
    val struct: Struct,
    val name: String,
    var valueType: Type
  )

  class Method(
    val name: String,
    var returnType: Option[Type],
    var precondition: Option[Expression] = None,
    var postcondition: Option[Expression] = None
  ) {
    // Variables/parameters are added to both a list and a map to preserve order and speedup lookup
    // Scope is a map of both parameters and variables
    private val _parameters = mutable.ListBuffer[Parameter]()
    private val _variables = mutable.ListBuffer[Var]()
    private val scope = mutable.Map[String, Var]()

    val body = new MethodBlock(this)

    def parameters: Seq[Parameter] = _parameters
    def variables: Seq[Var] = _variables

    def variable(name: String): Var =
      scope.getOrElse(name, throw new IRException(s"Variable '$name' not found"))

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, Helpers.findAvailableName(scope, name))
      scope += newParam.name -> newParam
      _parameters += newParam
      newParam
    }

    def addVar(valueType: Type, name: String = "_"): Var = {
      val newVar = new Var(valueType, Helpers.findAvailableName(scope, name))
      scope += newVar.name -> newVar
      _variables += newVar
      newVar
    }

    def getVar(name: String): Option[Var] = scope.get(name)
  }

  class Predicate(
    val name: String,
    var expression: IRGraph.Expression
  ) {
    private val _parameters = mutable.ListBuffer[Parameter]()

    def parameters: Seq[Parameter] = _parameters

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, name)
      _parameters += newParam
      newParam
    }
  }

  // Block is a mutable doubly-linked list of Op nodes
  // It implements a custom iterator which iterates over all Ops in order
  sealed trait Block extends Iterable[Op] {
    // Gets the method that this block is in
    def method: Method

    private[IRGraph] var headNode: Option[Op] = None
    private[IRGraph] var tailNode: Option[Op] = None

    private[IRGraph] def claim(op: Op): Unit = {
      if (op._block.isDefined)
        throw new IRException("Op is already added to a Block")
      op._block = Some(this)
    }

    // Appends an Op to the end of the block
    def += (newOp: Op): Unit = {
      claim(newOp)

      // Check if there is a existing tail
      tailNode match {
        // If there is, new.previous becomes the old tail
        // and the tail becomes the new node
        case Some(tailOp) => {
          // From: -> tailOp
          // To:   -> tailOp -> newOp
          newOp.previous = tailNode
          tailNode = Some(newOp)
          tailOp.next = tailNode
        }

        // Otherwise, it becomes a one-element list
        case None => {
          // There is no next or previous, and tail and head are the same
          headNode = Some(newOp)
          tailNode = headNode
        }
      }
    }

    private[IRGraph] def insertBefore(op: Op, newOp: Op): Unit = {
      claim(newOp)

      newOp.next = Some(op)

      op.previous match {
        case None => {
          headNode = Some(newOp)
        }
        case Some(prevOp) => {
          newOp.previous = op.previous
          prevOp.next = Some(newOp)
        }
      }

      op.previous = Some(newOp)
    }

    private[IRGraph] def insertAfter(op: Op, newOp: Op): Unit = {
      claim(newOp)

      newOp.previous = Some(op)
 
      op.next match {
        case None => {
          tailNode = Some(newOp)
        }

        case Some(nextOp) => {
          newOp.next = op.next
          nextOp.previous = Some(newOp)
        }
      }

      op.next = Some(newOp)
    }

    private[IRGraph] def remove(op: Op): Unit = {
      op.previous match {
        case None => headNode = op.next
        case Some(prevOp) => prevOp.next = op.next
      }

      op.next match {
        case None => tailNode = op.previous
        case Some(nextOp) => nextOp.previous = op.previous
      }

      op._block = None
    }

    def iterator: Iterator[Op] = new Iterator[Op] {
      var current: Option[Op] = headNode
      def hasNext: Boolean = current.isDefined
      def next(): Op = {
        val value = current.get
        current = value.next
        value
      }
    }
  }

  class MethodBlock(_method: Method) extends Block {
    def method: Method = _method
  }

  class ChildBlock(op: Op) extends Block {
    def method = op.block.method
  }

  sealed trait Expression

  class Parameter(valueType: Type, name: String) extends Var(valueType, name)
  class Var(var valueType: Type, val name: String) extends Expression

  sealed trait Member extends Expression {
    var root: Expression
    def valueType: Type
  }

  class FieldMember(var root: Expression, var field: StructField) extends Member {
    def valueType: Type = field.valueType
  }
  class DereferenceMember(var root: Expression, var valueType: Type) extends Member
  // TODO: Index should be Expression
  class ArrayMember(var root: Expression, var valueType: Type, var index: Int) extends Member

  class Accessibility(var member: Member) extends Expression

  class PredicateInstance(
    var predicate: Predicate,
    var arguments: List[IRGraph.Expression]) extends Expression

  // Represents a \result expression in a specification
  class Result(var method: Method) extends Expression

  // Wraps another expression and adds imprecision (i.e. `? && precise`)
  class Imprecise(var precise: Option[IRGraph.Expression]) extends Expression

  sealed trait Literal extends Expression
  class Int(val value: scala.Int) extends Literal
  class Char(val value: scala.Char) extends Literal
  class Bool(val value: scala.Boolean) extends Literal
  class Null extends Literal

  class Conditional(
    var condition: Expression,
    var ifTrue: Expression,
    var ifFalse: Expression
  ) extends Expression

  class Binary(
    var operator: BinaryOp,
    var left: Expression,
    var right: Expression
  ) extends Expression

  sealed trait BinaryOp
  object BinaryOp {
    object Add extends BinaryOp
    object Subtract extends BinaryOp
    object Divide extends BinaryOp
    object Multiply extends BinaryOp
    object And extends BinaryOp
    object Or extends BinaryOp
    object Equal extends BinaryOp
    object NotEqual extends BinaryOp
    object Less extends BinaryOp
    object LessOrEqual extends BinaryOp
    object Greater extends BinaryOp
    object GreaterOrEqual extends BinaryOp
  }

  class Unary(
    var operator: UnaryOp,
    var operand: Expression
  ) extends Expression

  sealed trait UnaryOp
  object UnaryOp {
    object Not extends UnaryOp
    object Negate extends UnaryOp
  }

  sealed trait Type {
    def name: String
    def default: IRGraph.Literal
  }

  // A pointer to a struct value
  class ReferenceType(val struct: Struct) extends Type {
    def name: String = "struct " + struct.name + "*"
    def default = new IRGraph.Null()
  }

  // A pointer to a primitive value
  class PointerType(val valueType: Type) extends Type {
    def name: String = valueType.name + "*"
    def default = new IRGraph.Null()
  }

  // An array of primitive values
  class ArrayType(val valueType: Type) extends Type {
    def name: String = valueType.name + "[]"
    def default = new IRGraph.Null()
  }

  // An array of struct values
  class ReferenceArrayType(val struct: Struct) extends Type {
    def name: String = "struct " + struct.name + "[]"
    def default = new IRGraph.Null()
  }

  object IntType extends Type {
    def name = "int"
    def default = new IRGraph.Int(0)
  }

  object BoolType extends Type {
    def name = "bool"
    def default = new IRGraph.Bool(false)
  }

  object CharType extends Type {
    def name = "char"
    def default = new IRGraph.Char(0)
  }

  // Represents a single operation, roughly equivalent to a C0 statement
  sealed trait Op {
    private[IRGraph] var _block: Option[Block] = None
    private[IRGraph] var previous: Option[Op] = None
    private[IRGraph] var next: Option[Op] = None

    def block: Block = _block.getOrElse(throw new IRException("Op does not belong to a block"))
    def method: Method = block.method

    def insertBefore(newOp: Op): Unit = block.insertBefore(this, newOp)
    def insertAfter(newOp: Op): Unit = block.insertAfter(this, newOp)

    // If this Op is not in a block, this is a no-op
    def remove(): Unit = _block.foreach(_.remove(this))
  }

  class Invoke(
    var callee: Method,
    var arguments: List[Expression],
    var target: Option[Expression]) extends Op

  class AllocValue(
    var valueType: Type,
    var target: Var
  ) extends Op

  class AllocStruct(
    var struct: Struct,
    var target: Expression
  ) extends Op

  // TODO: Length should be an expression
  class AllocArray(
    var valueType: Type,
    var length: Int,
    var target: Var) extends Op

  class Assign(
    var target: Var,
    var value: Expression
  ) extends Op

  class AssignMember(
    var member: Member,
    var value: Expression
  ) extends Op

  class Assert(
    var value: Expression,
    var kind: AssertKind
  ) extends Op

  sealed trait AssertKind
  object AssertKind {
    object Imperative extends AssertKind
    object Specification extends AssertKind
  }

  class Fold(
    var instance: PredicateInstance
  ) extends Op

  class Unfold(
    var instance: PredicateInstance
  ) extends Op

  class Error(
    var value: Expression
  ) extends Op

  class Return(var value: Option[Expression]) extends Op

  class If(
    var condition: Expression
  ) extends Op {
    val ifTrue = new ChildBlock(this)
    val ifFalse = new ChildBlock(this)
  }

  class While(
    var condition: Expression,
    var invariant: Option[Expression]
  ) extends Op {
    val body = new ChildBlock(this)
  }
}