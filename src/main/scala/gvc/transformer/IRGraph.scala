package gvc.transformer
import scala.collection.mutable

object IRGraph {
  sealed trait Node

  class IRException(message: String) extends Exception(message)

  class Program {
    private val _structs = mutable.Map[String, Struct]()
    private val _methods = mutable.Map[String, Method]()
    private val predicates = mutable.Map[String, Predicate]()

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
      if (predicates.getOrElseUpdate(predicate.name, predicate) != predicate)
        throw new IRException(s"Predicate '${predicate.name}' already exists")
      predicate
    }

    def structs = _structs.toSeq
      .sortBy({ case (k, _) => k })
      .map({ case (_, v) => v })

    def methods = _methods.toSeq
      .sortBy({ case (k, _) => k })
      .map({ case (_, v) => v })

    def getStruct(name: String) = _structs.get(name).getOrElse(throw new IRException(s"Struct '$name' not found"))
    def getMethod(name: String) = _methods.get(name).getOrElse(throw new IRException(s"Method '$name' not found"))
    def getPredicate(name: String) = predicates.get(name).getOrElse(throw new IRException(s"Predicate '$name' not found"))
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

    val entry = new BasicBlock(this, None)

    def parameters: Seq[Parameter] = params.toSeq

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, getAvailableName(name))
      scope += newParam.name -> newParam
      params += newParam
      newParam
    }

    def addVar(valueType: Type, name: String = "_"): Var = {
      val newVar = new Var(valueType, getAvailableName(name))
      scope += newVar.name -> newVar
      vars += newVar
      newVar
    }

    private def getAvailableName(name: String) =
      Iterator.from(0).map(_ match {
        case 0 => name
        case n => name + n
      }).find(!scope.contains(_)).get

    def variables: Seq[Var] = vars.toSeq
  }

  class Predicate(
    var name: String,
    var expression: IRGraph.Expression
  ) {
    private val params = mutable.ArrayBuffer[Parameter]()

    def parameters = params.toSeq

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, name)
      params += newParam
      newParam
    }
  }

  sealed trait Block extends Node {
    var method: Method
    var previous: Option[Block]
    var next: Option[Block]

    def predecessors: Seq[IRGraph.Block] = previous match {
      case None => Seq.empty
      case Some(basic: BasicBlock) => Seq(basic)
      case Some(iff: IfBlock) => Seq(iff.ifTrue, iff.ifFalse)
      case Some(whil: WhileBlock) => whil.predecessors :+ whil.body
    }
  }

  class BasicBlock(
    var method: Method,
    var previous: Option[Block],
  ) extends Block {
    var next: Option[Block] = None
    val ops = mutable.ArrayBuffer[Op]()
  }

  class IfBlock(
    var method: Method,
    var previous: Option[Block],
    var condition: IRGraph.Expression
  ) extends Block {
    var next: Option[Block] = None
    val ifTrue = new BasicBlock(method, previous)
    val ifFalse = new BasicBlock(method, previous)
  }

  class WhileBlock(
    var method: Method,
    var previous: Option[Block],
    var condition: IRGraph.Expression,
    var invariant: Option[IRGraph.Expression] = None
  ) extends Block {
    var next: Option[Block] = None
    val body = new BasicBlock(method, previous)
  }

  sealed trait Expression extends Node

  class Parameter(valueType: Type, name: String) extends Var(valueType, name)
  class Var(var valueType: Type, val name: String) extends Expression

  class Member(var instance: Expression, var field: StructField) extends Expression

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

  class Dereference(
    var valueType: Type,
    var value: Expression
  ) extends Expression

  sealed trait Type extends Node {
    def name: String
    def default: IRGraph.Literal
  }

  class ReferenceType(val struct: Struct) extends Type {
    def name = "struct " + struct.name + "*"
    def default = new IRGraph.Null()
  }

  class PointerType(val valueType: Type) extends Type {
    def name = valueType.name + "*"
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

  sealed trait Op extends Node

  class Invoke(
    var method: Method,
    var arguments: List[Expression],
    var target: Option[Var]) extends Op

  class AllocValue(
    var valueType: Type,
    var target: Var
  ) extends Op

  class AllocStruct(
    var struct: Struct,
    var target: Var
  ) extends Op

  class Assign(
    var target: Var,
    var value: Expression
  ) extends Op

  class AssignMember(
    var target: Expression,
    var field: StructField,
    var value: Expression
  ) extends Op

  class AssignPointer(
    var target: Expression,
    var value: Expression,
    var valueType: Type
  ) extends Op

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

  class Return(
    var value: Option[Expression],
    var method: Method
  ) extends Op
}