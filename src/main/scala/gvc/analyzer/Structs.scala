package gvc.analyzer
import gvc.parser._

case class ResolvedStructDeclaration(
  parsed: StructDefinition,
  name: String,
)

case class ResolvedStructDefinition(
  parsed: StructDefinition,
  declaration: ResolvedStructDeclaration,
  fields: List[ResolvedStructField]
) {
  def name = declaration.name

  def lookupField(name: String): Option[ResolvedStructField] =
    fields.find(_.name == name)
}

case class ResolvedStructField(
  parsed: MemberDefinition,
  name: String,
  valueType: ResolvedType,
)
