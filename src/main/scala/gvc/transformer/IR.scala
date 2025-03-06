package gvc.transformer
import scala.collection.mutable

class IRException(message: String) extends Exception(message)

object IR {
  // Note that names of methods, vars, etc. are immutable, since they are also copied in their respective Maps
  class Program {
    private[IR] var _structs =
      mutable.Map[String, StructDefinition]()
    private[IR] var _methods =
      mutable.Map[String, MethodDefinition]()
    private var _predicates = mutable.Map[String, Predicate]()
    private var _dependencies = mutable.ListBuffer[Dependency]()

    lazy val ownedFieldsStruct = struct(
      Helpers.findAvailableName(_structs, "OwnedFields")
    )

    def addDependency(
        path: String,
        isLibrary: Boolean
    ): Dependency = {
      if (_dependencies.exists(d => d.path == path && d.isLibrary == isLibrary))
        throw new IRException(s"Dependency '$path' already exists")

      val newDep = new Dependency(this, path, isLibrary)
      _dependencies += newDep
      newDep
    }

    def addMethod(
        name: String,
        returnType: Option[Type]
    ): Method = {
      val method = new Method(name, returnType)
      if (_methods.getOrElseUpdate(method.name, method) != method)
        throw new IRException(s"Method '${method.name}' already exists")
      method
    }

    def addPredicate(name: String): Predicate = {
      val predicate = new Predicate(name, new IR.BoolLit(true))
      if (_predicates.getOrElseUpdate(predicate.name, predicate) != predicate)
        throw new IRException(s"Predicate '${predicate.name}' already exists")
      predicate
    }

    def structs: Seq[Struct] = _structs.values
      .collect { case (s: Struct) => s }
      .toSeq
      .sortBy(_.name)

    def methods: Seq[Method] = _methods.values
      .collect { case (m: Method) => m }
      .toSeq
      .sortBy(_.name)

    def predicates: Seq[Predicate] = _predicates.values.toSeq.sortBy(_.name)

    def dependencies: Seq[Dependency] = _dependencies.toList.sortBy(_.path)

    // Structs can be used even if they are never declared
    def struct(name: String): StructDefinition =
      _structs.getOrElseUpdate(name, new Struct(name))

    def structDef(name: String): Struct =
      _structs(name) match {
        case s: Struct => s
        case _: DependencyStruct =>
          throw new IRException("Cannot get definition for struct declared in library")
      }

    // Adds a new struct, renaming it if necessary to avoid collisions
    def newStruct(name: String): Struct = {
      val actualName = Helpers.findAvailableName(_structs, name)
      val struct = new Struct(actualName)
      _structs += actualName -> struct
      struct
    }

    def method(name: String): MethodDefinition =
      _methods.getOrElse(
        name,
        throw new IRException(s"Method '$name' not found")
      )

    def methodBody(name: String): Option[MethodBlock] =
      _methods.values
        .collect { case (m: Method) => m }
        .find(_.name.equals(name)) match {
        case Some(value) => Some(value.body)
        case None        => None
      }

    def predicate(name: String): Predicate = _predicates.getOrElse(
      name,
      throw new IRException(s"Predicate '$name' not found")
    )

    def replaceMethods(methodList: Seq[MethodDefinition]): Unit =
      _methods = methodList.foldLeft(
        mutable.Map[String, MethodDefinition]()
      )((m, defn) => {
        m + (defn.name -> defn)
      })

    def replacePredicates(predicateList: Seq[Predicate]): Unit =
      _predicates = predicateList.foldLeft(
        mutable.Map[String, Predicate]()
      )((m, pred) => { m + (pred.name -> pred) })

    def copy(methods: Seq[Method], predicates: Seq[Predicate]) = {
      val newProgram = new IR.Program()

      newProgram.replacePredicates(predicates)
      newProgram.replaceMethods(methods)

      newProgram._structs = _structs.map(str => {
        val replacement = new Struct(str._1)
        str._2.fields.foreach(fld => {
          replacement.addField(fld.name, fld.valueType)
        })
        replacement.name -> replacement
      })

      newProgram._dependencies = mutable.ListBuffer()
      _dependencies.foreach(newProgram._dependencies += _)
      newProgram
    }
  }

  sealed trait StructDefinition {
    def name: String
    def fields: Seq[StructField]
  }

  class Struct(val name: String) extends StructDefinition {
    private val _fields = mutable.ListBuffer[StructField]()

    def addField(name: String, valueType: Type): StructField = {
      val field = new StructField(
        this,
        Helpers.findAvailableName(_fields.map(_.name), name),
        valueType
      )
      _fields += field
      field
    }
    def fields: Seq[StructField] = _fields
  }

  class StructField(
      val struct: StructDefinition,
      val name: String,
      var valueType: Type
  )

  sealed trait MethodDefinition {
    def name: String
    def returnType: Option[Type]
    def parameters: Seq[Parameter]
  }

  class Method(
      val name: String,
      var returnType: Option[Type],
      var precondition: Option[Expression] = None,
      var postcondition: Option[Expression] = None,
  ) extends MethodDefinition {
    // Variables/parameters are added to both a list and a map to preserve order and speedup lookup
    // Scope is a map of both parameters and variables
    private var _parameters = mutable.ListBuffer[Parameter]()
    private var _variables = mutable.ListBuffer[Var]()
    private var scope = mutable.Map[String, Var]()

    var body = new MethodBlock(this)

    def parameters: Seq[Parameter] = _parameters
    def variables: Seq[Var] = _variables

    def variable(name: String): Var =
      scope.getOrElse(
        name,
        throw new IRException(s"Variable '$name' not found")
      )

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam =
        new Parameter(valueType, Helpers.findAvailableName(scope, name))
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

    def copy(
        replacementPre: Option[Expression] = precondition,
        replacementPost: Option[Expression] = postcondition,
        replacementBody: List[Op] = body.toList
    ): Method = {
      val copyOf = new Method(name, returnType, replacementPre, replacementPost)
      _variables.foreach(v => copyOf.addVar(v.varType, v.name))
      _parameters.foreach(p => copyOf.addParameter(p.varType, p.name))
      scope.foreach(entry => {
        if (!copyOf.scope.contains(entry._1)) {
          copyOf.scope += entry._1 -> new IR.Var(
            entry._2.varType,
            entry._2.name
          )
        }
      })

      replacementBody.foreach(copyOf.body += _.copy)
      copyOf
    }
  }
  class Predicate(
      val name: String,
      var expression: IR.Expression
  ) {
    private var _parameters = mutable.ListBuffer[Parameter]()

    def parameters: Seq[Parameter] = _parameters

    def addParameter(valueType: Type, name: String): Parameter = {
      val newParam = new Parameter(valueType, name)
      _parameters += newParam
      newParam
    }
    def copy(expr: Expression) = {
      val newPred = new Predicate(name, expr)
      newPred._parameters = _parameters
      newPred
    }
  }

  // Block is a mutable doubly-linked list of Op nodes
  // It implements a custom iterator which iterates over all Ops in order
  sealed trait Block extends Iterable[Op] {
    // Gets the method that this block is in
    def method: Method

    private[IR] var headNode: Option[Op] = None
    private[IR] var tailNode: Option[Op] = None

    private[IR] def claim(op: Op): Unit = {
      if (op._block.isDefined)
        throw new IRException("Op is already added to a Block")
      op._block = Some(this)
    }

    // Appends an Op to the end of the block
    def +=(newOp: Op): Unit = {
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

    def ++=(newOps: Seq[Op]): Unit = {
      for (op <- newOps) +=(op)
    }

    // Prepends an Op to the beginning of the block
    def +=:(newOp: Op): Unit = {
      claim(newOp)

      // Check if there is a existing head
      headNode match {
        // If there is, new.next becomes the old head
        // and the head becomes the new node
        case Some(headOp) => {
          // From: headOp ->
          // To:   newOp -> headOp ->
          newOp.next = headNode
          headNode = Some(newOp)
          headOp.previous = headNode
        }

        // Otherwise, it becomes a one-element list
        case None => {
          // There is no next or previous, and tail and head are the same
          headNode = Some(newOp)
          tailNode = headNode
        }
      }
    }

    def ++=:(newOps: Seq[Op]): Unit = {
      // TODO: This could be implemented better
      newOps.toList match {
        case Nil => ()
        case head :: tl => {
          +=:(head)
          head.insertAfter(tl)
        }
      }
    }

    private[IR] def insertBefore(op: Op, newOp: Op): Unit = {
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

    private[IR] def insertAfter(op: Op, newOp: Op): Unit = {
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

    private[IR] def remove(op: Op): Unit = {
      op.previous match {
        case None         => headNode = op.next
        case Some(prevOp) => prevOp.next = op.next
      }

      op.next match {
        case None         => tailNode = op.previous
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

    override def lastOption: Option[Op] = tailNode
    override def last: Op = tailNode.get
  }

  class MethodBlock(_method: Method) extends Block {
    def method: Method = _method
  }

  class ChildBlock(val op: Op) extends Block {
    def method = op.block.method
  }

  sealed trait Expression {
    def valueType: Option[Type]

    def contains(exp: Expression): Boolean =
      exp == this

    override def toString() = IRPrinter.print(this)
  }

  class Parameter(varType: Type, name: String)
      extends Var(varType, name)
  class Var(var varType: Type, val name: String)
      extends Expression {
    def valueType: Option[Type] = Some(varType)
  }

  sealed trait Member extends Expression {
    var root: Expression
    override def contains(exp: Expression) =
      super.contains(exp) || root.contains(exp)
  }

  class FieldMember(var root: Expression, var field: StructField)
      extends Member {
    def valueType: Option[Type] = Some(field.valueType)
  }
  class DereferenceMember(var root: Expression) extends Member {
    def valueType: Option[Type] = root.valueType match {
      case Some(ptr: PointerType) => Some(ptr.valueType)
      case _                      => None
    }
  }
  class ArrayMember(var root: Expression, var index: Expression)
      extends Member {
    def valueType: Option[Type] = root.valueType match {
      case Some(arr: ArrayType) => Some(arr.valueType)
      case _                    => None
    }
  }

  // Expressions that can only be used within specifications
  sealed trait SpecificationExpression extends Expression {
    def valueType: Option[Type] = None
  }

  class Accessibility(var member: Member) extends SpecificationExpression {
    override def contains(exp: Expression) =
      super.contains(exp) || member.contains(exp)

  }

  class PredicateInstance(
      var predicate: Predicate,
      var arguments: List[IR.Expression]
  ) extends SpecificationExpression {
    override def contains(exp: Expression) =
      super.contains(exp) || arguments.exists(_.contains(exp))
    override def toString() =
      predicate.name + "(" + arguments.map(IRPrinter.print).mkString(", ") + ")"
  }

  // "unfolding" expressions in a specification
  class Unfolding(
    var instance: PredicateInstance,
    var expr: IR.Expression
  ) extends SpecificationExpression {
    override def contains(exp: Expression) =
      super.contains(exp) || instance.contains(exp) || expr.contains(exp)
    override def valueType: Option[Type] = expr.valueType
  }

  // Represents a \result expression in a specification
  class Result(var method: Method) extends SpecificationExpression {
    override def valueType = method.returnType
  }

  // Wraps another expression and adds imprecision (i.e. `? && precise`)
  class Imprecise(var precise: Option[IR.Expression])
      extends SpecificationExpression {
    override def contains(exp: Expression) =
      super.contains(exp) || precise.exists(_.contains(exp))
  }

  sealed trait Literal extends Expression
  class IntLit(val value: Int) extends Literal {
    def valueType: Option[Type] = Some(IntType)
  }
  class CharLit(val value: scala.Char) extends Literal {
    def valueType: Option[Type] = Some(CharType)
  }
  class BoolLit(val value: scala.Boolean) extends Literal {
    def valueType: Option[Type] = Some(BoolType)
  }
  class StringLit(val value: String) extends Literal {
    def valueType: Option[Type] = Some(StringType)
  }
  class NullLit extends Literal {
    def valueType: Option[Type] = None
  }

  class Conditional(
      var condition: Expression,
      var ifTrue: Expression,
      var ifFalse: Expression
  ) extends Expression {
    def valueType: Option[Type] = ifTrue.valueType.orElse(ifFalse.valueType)
    override def contains(exp: Expression): Boolean =
      super.contains(exp) || condition.contains(exp) || ifTrue.contains(
        exp
      ) || ifFalse.contains(exp)
  }

  class Binary(
      var operator: BinaryOp,
      var left: Expression,
      var right: Expression
  ) extends Expression {
    def valueType: Option[Type] = operator match {
      case BinaryOp.Add | BinaryOp.Subtract | BinaryOp.Divide |
          BinaryOp.Multiply =>
        Some(IntType)
      case BinaryOp.And | BinaryOp.Or | BinaryOp.Equal | BinaryOp.NotEqual |
          BinaryOp.Less | BinaryOp.LessOrEqual | BinaryOp.Greater |
          BinaryOp.GreaterOrEqual =>
        Some(BoolType)
    }
    override def contains(exp: Expression): Boolean =
      super.contains(exp) || left.contains(exp) || right.contains(exp)
  }

  sealed trait BinaryOp
  object BinaryOp {
    object Add extends BinaryOp { override def toString() = "+" }
    object Subtract extends BinaryOp { override def toString() = "-" }
    object Divide extends BinaryOp { override def toString() = "/" }
    object Multiply extends BinaryOp { override def toString() = "*" }
    object And extends BinaryOp { override def toString() = "&&" }
    object Or extends BinaryOp { override def toString() = "||" }
    object Equal extends BinaryOp { override def toString() = "==" }
    object NotEqual extends BinaryOp { override def toString() = "!=" }
    object Less extends BinaryOp { override def toString() = "<" }
    object LessOrEqual extends BinaryOp { override def toString() = "<=" }
    object Greater extends BinaryOp { override def toString() = ">" }
    object GreaterOrEqual extends BinaryOp { override def toString() = ">=" }
  }

  class Unary(
      var operator: UnaryOp,
      var operand: Expression
  ) extends Expression {
    def valueType: Option[Type] = operator match {
      case UnaryOp.Negate => Some(IntType)
      case UnaryOp.Not    => Some(BoolType)
    }
    override def contains(exp: Expression) =
      super.contains(exp) || operand.contains(exp)
  }

  sealed trait UnaryOp
  object UnaryOp {
    object Not extends UnaryOp { override def toString() = "!" }
    object Negate extends UnaryOp { override def toString() = "-" }
  }

  sealed trait Type {
    def name: String
    def default: IR.Literal
  }

  // A pointer to a struct value
  class ReferenceType(val struct: StructDefinition) extends Type {
    def name: String = "struct " + struct.name + "*"
    def default = new IR.NullLit()
  }

  // A pointer to a primitive value
  class PointerType(val valueType: Type) extends Type {
    def name: String = valueType.name + "*"
    def default = new IR.NullLit()
  }

  // An array of primitive values
  class ArrayType(val valueType: Type) extends Type {
    def name: String = valueType.name + "[]"
    def default = new IR.NullLit()
  }

  // An array of struct values
  class ReferenceArrayType(val struct: StructDefinition) extends Type {
    def name: String = "struct " + struct.name + "[]"
    def default = new IR.NullLit()
  }

  object IntType extends Type {
    def name = "int"
    def default = new IR.IntLit(0)
  }

  object BoolType extends Type {
    def name = "bool"
    def default = new IR.BoolLit(false)
  }

  object CharType extends Type {
    def name = "char"
    def default = new IR.CharLit(0)
  }

  object StringType extends Type {
    def name = "string"
    def default = new IR.CharLit(0)
  }

  // Represents a single operation, roughly equivalent to a C0 statement
  sealed trait Op {
    private[IR] var _block: Option[Block] = None
    private[IR] var previous: Option[Op] = None
    private[IR] var next: Option[Op] = None

    def getPrev: Option[Op] = previous
    def getNext: Option[Op] = next

    def block: Block =
      _block.getOrElse(throw new IRException("Op does not belong to a block"))
    def method: Method = block.method

    def insertBefore(newOp: Op): Unit = block.insertBefore(this, newOp)
    def insertBefore(opList: Seq[Op]): Unit =
      opList.foreach(newOp => block.insertBefore(this, newOp))

    def insertAfter(newOp: Op): Unit = block.insertAfter(this, newOp)
    def insertAfter(opList: Seq[Op]): Unit =
      opList.foldLeft(this)((at, newOp) => {
        block.insertAfter(at, newOp)
        newOp
      })

    // If this Op is not in a block, this is a no-op
    def remove(): Unit = _block.foreach(_.remove(this))

    // Creates a copy of the current Op
    // The new copy will not be attached to any Block
    def copy: IR.Op

    def summary: String
  }

  class Invoke(
      var callee: MethodDefinition,
      var arguments: List[Expression],
      var target: Option[Expression]
  ) extends Op {
    def copy = new Invoke(callee, arguments, target)
    def summary = (
      target.map(e => IRPrinter.print(e) + " = ").getOrElse("")
        + callee.name + "(" + arguments.map(IRPrinter.print) + ")"
    )
  }

  class AllocValue(
      var valueType: Type,
      var target: Var
  ) extends Op {
    def copy = new AllocValue(valueType, target)
    def summary = target.name + " = alloc(" + valueType.name + ")"
  }

  class AllocStruct(
      var struct: StructDefinition,
      var target: Expression
  ) extends Op {
    def copy = new AllocStruct(struct, target)
    def summary =
      IRPrinter.print(target) + " = alloc(struct " + struct.name + ")"
  }

  // TODO: Length should be an expression
  class AllocArray(
      var valueType: Type,
      var length: IntLit,
      var target: Var
  ) extends Op {
    def copy = new AllocArray(valueType, length, target)
    def summary = (
      IRPrinter.print(target)
      + "= alloc_array(" + valueType.name
      + ", " + IRPrinter.print(length) + ")"
    )
  }

  class Assign(
      var target: Var,
      var value: Expression
  ) extends Op {
    def copy = new Assign(target, value)
    def summary = target.name + " = " + IRPrinter.print(value)
  }

  class AssignMember(
      var member: Member,
      var value: Expression
  ) extends Op {
    def copy = new AssignMember(member, value)
    def summary = IRPrinter.print(member) + " = " + IRPrinter.print(value)
  }

  class Assert(
      var value: Expression,
      var kind: AssertKind
  ) extends Op {
    def copy = new Assert(value, kind)
    def summary = (kind match {
      case IR.AssertKind.Imperative => "assert "
      case IR.AssertKind.Specification => "//@assert "
    }) + IRPrinter.print(value)
  }

  sealed trait AssertKind
  object AssertKind {
    object Imperative extends AssertKind
    object Specification extends AssertKind
  }

  class Fold(
      var instance: PredicateInstance
  ) extends Op {
    def copy = new Fold(instance)
    def summary = "//@fold " + instance.toString()
  }

  class Unfold(
      var instance: PredicateInstance
  ) extends Op {
    def copy = new Unfold(instance)
    def summary = "//@unfold " + instance.toString()
  }

  class Error(
      var value: Expression
  ) extends Op {
    def copy = new Error(value)
    def summary = "error(" + IRPrinter.print(value) + ")"
  }

  class Return(var value: Option[Expression]) extends Op {
    def copy = new Return(value)
    def summary = value match {
      case None => "return"
      case Some(e) => "return " + IRPrinter.print(e)
    }
  }

  class If(
      var condition: Expression
  ) extends Op {
    val ifTrue = new ChildBlock(this)
    val ifFalse = new ChildBlock(this)

    def copy = {
      val newIf = new If(condition)
      ifTrue.foreach(newIf.ifTrue += _.copy)
      ifFalse.foreach(newIf.ifFalse += _.copy)
      newIf
    }
    def copy(trueBranch: List[Op], falseBranch: List[Op]) = {
      val newIf = new If(condition)
      trueBranch.foreach(newIf.ifTrue += _.copy)
      falseBranch.foreach(newIf.ifFalse += _.copy)
      newIf
    }

    def summary = "if (" + IRPrinter.print(condition) + ") ..."
  }

  class While(
      var condition: Expression,
      var invariant: Expression
  ) extends Op {
    var body = new ChildBlock(this)

    def copy = {
      val newWhile = new While(condition, invariant)
      body.foreach(newWhile.body += _.copy)
      newWhile
    }
    def copy(
        newInvariant: IR.Expression,
        newBody: List[IR.Op]
    ) = {
      val newWhile = new While(condition, newInvariant)
      newBody.foreach(newWhile.body += _.copy)
      newWhile
    }

    def summary = "while (" + IRPrinter.print(condition) + ") ..."
  }

  class Dependency(
      program: Program,
      val path: String,
      val isLibrary: Boolean
  ) {
    private val _methods = mutable.ListBuffer[DependencyMethod]()
    private val _structs = mutable.ListBuffer[DependencyStruct]()

    def methods: Seq[DependencyMethod] = _methods
    def structs: Seq[DependencyStruct] = _structs

    def defineMethod(
        name: String,
        returnType: Option[Type]
    ): DependencyMethod = {
      if (program._methods.contains(name)) {
        throw new IRException(
          s"Method '$name' already exists (importing from '$path'"
        )
      }

      val method = new DependencyMethod(name, returnType)
      program._methods += method.name -> method
      _methods += method
      method
    }

    def defineStruct(name: String): DependencyStruct = {
      val struct = new DependencyStruct(name)
      if (_structs.contains(struct.name)) {
        // TODO: This should not throw if the struct *fields* have not been defined
        throw new IRException(
          s"Struct '${struct.name}' already exists (importing from '$path'"
        )
      }

      program._structs += struct.name -> struct
      _structs += struct
      struct
    }
  }

  class DependencyStruct(val name: String)
      extends StructDefinition {
    private val _fields = mutable.ListBuffer[StructField]()

    def fields: Seq[StructField] = _fields

    def addField(
        fieldName: String,
        valueType: Type
    ): StructField = {
      val field = new StructField(this, fieldName, valueType)
      if (_fields.exists(_.name == fieldName))
        throw new TransformerException(
          s"Field '$name.$fieldName' already exists"
        )
      _fields += field
      field
    }
  }

  class DependencyMethod(
      val name: String,
      val returnType: Option[Type]
  ) extends MethodDefinition {
    val _parameters = mutable.ListBuffer[Parameter]()

    def parameters: Seq[Parameter] = _parameters

    def addParameter(name: String, valueType: Type): Parameter = {
      val param = new Parameter(valueType, name)
      if (_parameters.exists(_.name == name))
        throw new TransformerException(s"Parameter '$name' already exists")
      _parameters += param
      param
    }
  }
}
