package gvc.analyzer
import gvc.parser._
import scala.collection.immutable.HashMap

sealed trait ResolvedType {
  def name: String
  def isEquivalent(other: ResolvedType): Boolean
}

case object UnknownType extends ResolvedType {
  def name: String = "<unknown>"

  // Just assume that an unknown type is any other type
  def isEquivalent(other: ResolvedType): Boolean = true
}

case class MissingNamedType(name: String) extends ResolvedType {
  // Assome that types with the same name are equivalent, even if they have
  // not been defined
  def isEquivalent(other: ResolvedType): Boolean = other match {
    case _: MissingNamedType => other.name == name
    case _ => false
  }
}

case class ResolvedStructType(
  structName: String
) extends ResolvedType {
  def name = "struct " + structName

  def isEquivalent(other: ResolvedType): Boolean = other match {
    case ResolvedStructType(otherName) => structName == otherName
    case _ => false
  }
}

case class ResolvedPointer(
  valueType: ResolvedType
) extends ResolvedType {
  def name = valueType.name + "*"

  def isEquivalent(other: ResolvedType) = other match {
    case ResolvedPointer(otherValue) => valueType.isEquivalent(otherValue)
    case NullType => true
    case _ => false
  }
}

case class ResolvedArray(
  valueType: ResolvedType
) extends ResolvedType {
  def name = valueType.name + "[]"

  def isEquivalent(other: ResolvedType): Boolean = other match {
    case ResolvedArray(otherType) => valueType.isEquivalent(otherType)
    case _ => false
  }
}

sealed trait BuiltinType extends ResolvedType {
  def isEquivalent(other: ResolvedType): Boolean = other match {
    case builtin: BuiltinType => builtin == this
    case _ => false
  }
}

object BuiltinType {
  val lookup = Map(
    "int" -> IntType,
    "string" -> StringType,
    "bool" -> BoolType,
    "char" -> CharType,
    "void" -> VoidType
  )
}

case object IntType extends BuiltinType {
  def name = "int"
}
case object StringType extends BuiltinType {
  def name = "string"
}
case object CharType extends BuiltinType {
  def name = "char"
}
case object BoolType extends BuiltinType {
  def name = "bool"
}

case object NullType extends BuiltinType {
  def name = "NULL"

  override def isEquivalent(other: ResolvedType): Boolean = other match {
    case ResolvedPointer(_) => true
    case NullType => true
    case _ => false
  }
}

case object VoidType extends BuiltinType {
  def name = "void"

  // void can never be used as a value of any type
  override def isEquivalent(other: ResolvedType): Boolean = false
}

case class ResolvedTypeDef(
  parsed: TypeDefinition,
  name: String,
  actualType: ResolvedType,
)