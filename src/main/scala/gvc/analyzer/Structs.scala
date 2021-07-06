package gvc.analyzer
import gvc.parser._

case class ResolvedStructDefinition(
  parsed: StructDefinition,
  name: String,
  fields: List[ResolvedStructField]
) {
  def lookupField(name: String): Option[ResolvedStructField] =
    fields.find(_.name == name)
}

case class ResolvedStructField(
  parsed: MemberDefinition,
  name: String,
  valueType: ResolvedType,
)
