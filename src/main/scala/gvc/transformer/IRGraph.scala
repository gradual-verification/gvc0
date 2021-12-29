package gvc.transformer
import scala.collection.mutable

object IRGraph {
  sealed trait Node

  class IRException(message: String) extends Exception(message)

  class Program {
    private val _structs = mutable.Map[String, Struct]()
    private val _methods = mutable.Map[String, Method]()
    private val _predicates = mutable.Map[String, Predicate]()

    def addStruct(name: String): Struct = {
      val struct = new Struct(name)
      if (_structs.getOrElseUpdate(struct.name, struct) != struct)
        throw new IRException(s"Struct '${struct.name}' already exists")
      struct
    }
    
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

  class Struct(var name: String) extends Node {
    private val _fields = mutable.ArrayBuffer[StructField]()

    def addField(name: String, valueType: Type): StructField = {
      val field = new StructField(this, name, valueType)
      _fields += field
      field
    }

    def fields: Seq[StructField] = _fields
  }

  class StructField(
    var struct: Struct,
    var name: String,
    var valueType: Type
  ) extends Node

  class Method(
    var name: String,
    var returnType: Option[Type],
    var precondition: Option[Expression] = None,
    var postcondition: Option[Expression] = None
  ) extends Node {
    private val params = mutable.ArrayBuffer[Parameter]()
    private val vars = mutable.ArrayBuffer[Var]()
    private val scope = mutable.Map[String, Var]()

    val body = new Block()

    def parameters: Seq[Parameter] = params

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, getAvailableName(name))
      scope += newParam.name -> newParam
      params += newParam
      newParam
    }

    def addVar(valueType: Type, name: String = "_"): Var = {
      val newVar = new Var(valueType, getAvailableName(name))
      addExistingVar(newVar)
      newVar
    }

    def addExistingVar(newVar: Var): Unit = {
      scope += newVar.name -> newVar
      vars += newVar
    }

    def getVar(name: String) = scope.get(name)

    private def getAvailableName(name: String) =
      Iterator.from(0).map {
        case 0 => name
        case n => name + n
      }.find(!scope.contains(_)).get

    def variable(name: String): Var =
      scope.getOrElse(name, throw new IRException(s"Variable '$name' not found"))

    def variables: Seq[Var] = vars
  }

  class Predicate(
    var name: String,
    var expression: IRGraph.Expression
  ) {
    private val params = mutable.ArrayBuffer[Parameter]()

    def parameters:Seq[Parameter] = params

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, name)
      params += newParam
      newParam
    }
  }

  class Block extends Iterable[Op] {
    private[IRGraph] var blockHead: Option[Op] = None
    private[IRGraph] var blockTail: Option[Op] = None

    private[IRGraph] def claim(op: Op): Unit = {
      if (op.block.isDefined) {
        println("here")
        throw new IRException("Cannot insert already-inserted Op")
      }
      op.block = Some(this)
    }

    def += (op: Op): Unit = blockTail match {
      case Some(tailOp) => tailOp.insertAfter(op)
      case None => {
        claim(op)
        blockHead = Some(op)
        blockTail = blockHead
      }
    }

    def iterator: Iterator[Op] = new Iterator[Op] {
      var current: Option[Op] = blockHead
      def hasNext: Boolean = current.isDefined
      def next(): Op = {
        val value = current.get
        current = value.next
        value        
      }
    }
  }

  sealed trait Expression extends Node

  class Parameter(valueType: Type, name: String) extends Var(valueType, name)
  class Var(var valueType: Type, val name: String) extends Expression

  sealed trait Member extends Expression {
    var root: Expression
  }

  class FieldMember(var root: Expression, var field: StructField) extends Member
  class DereferenceMember(var root: Expression, var valueType: Type) extends Member
  // TODO: Index should be Expression
  class ArrayMember(var root: Expression, var valueType: Type, var index: Int) extends Member

  class Accessibility(var member: Member) extends Expression

  class PredicateInstance(
    var predicate: Predicate,
    var arguments: List[IRGraph.Expression]) extends Expression

  class Result(var method: Method) extends Expression

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

  sealed trait Type extends Node {
    def name: String
    def default: IRGraph.Literal
  }


  class ReferenceType(val struct: Struct) extends Type {
    def name: String = "struct " + struct.name + "*"
    def default = new IRGraph.Null()
  }

  class PointerType(val valueType: Type) extends Type {
    def name: String = valueType.name + "*"
    def default = new IRGraph.Null()
  }

  class ArrayType(val valueType: Type) extends Type {
    def name: String = valueType.name + "[]"
    def default = new IRGraph.Null()
  }

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

  sealed trait Op {
    private[IRGraph] var block: Option[Block] = None
    private[IRGraph] var previous: Option[Op] = None
    private[IRGraph] var next: Option[Op] = None

    def insertBefore(op: Op): Unit = {
      val b = block.getOrElse(throw new IRException("Cannot insert before an Op that has not been added to a Block"))
      b.claim(op)

      previous match {
        case Some(prevOp) =>
          prevOp.next = Some(op)
          op.next = Some(this)
          previous = Some(op)
        case None =>
          // If there is no previous, the current node must be the head node
          previous = Some(op)
          b.blockHead = previous
          op.next = Some(this)
      }
    }
    def insertBefore(opSeq: Seq[Op]): Unit = {
      opSeq.foreach(op => {
        insertBefore(op)
      })
    }

    def insertAfter(op: Op): Unit = {
      val b = block.getOrElse(throw new IRException("Cannot insert before an Op that has not been added to a Block"))
      b.claim(op)

      op.previous = Some(this)
      next match {
        case Some(nextOp) => {
          nextOp.previous = Some(op)
          op.next = Some(nextOp)
        }
        case None => {
          // If there is no next, then the current node is the current tail
          // Update the tail to be the new appended node
          b.blockTail = Some(op)
        }
      }

      next = Some(op)
    }
    def insertAfter(opSeq: Seq[Op]): Unit = {
      opSeq.foreach(op => {
        insertAfter(op)
      })
    }
  }

  class Invoke(
    var method: Method,
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

  class AllocArray(var valueType: Type, var length: Int, var target: Var) extends Op

  class Assign(
    var target: Var,
    var value: Expression
  ) extends Op

  class AssignMember(
    var member: Member,
    var value: Expression
  ) extends Op

  class AssignIndex(var target: Var, var index: Int, var value: Expression) extends Op

  class Assert(
    var value: Expression,
    var method: AssertMethod
  ) extends Op

  sealed trait AssertMethod
  object AssertMethod {
    object Imperative extends AssertMethod
    object Specification extends AssertMethod
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

  class Return(var method: Method) extends Op

  class ReturnValue(
    var value: Expression,
    method: Method
  ) extends Return(method)

  class ReturnInvoke(
    var invoke: Method,
    var arguments: List[Expression],
    method: Method
  ) extends Return(method)

  class If(
    var condition: Expression
  ) extends Op {
    val ifTrue = new Block()
    val ifFalse = new Block()
  }

  class While(
    var condition: Expression,
    var invariant: Option[Expression]
  ) extends Op {
    val body = new Block()
  }
}