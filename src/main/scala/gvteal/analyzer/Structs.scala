package gvc.analyzer
import gvc.parser._

case class ResolvedStructDefinition(
  parsed: StructDefinition,
  name: String,
  fields: List[ResolvedStructField]
) extends ResolvedNode {
  def lookupField(name: String): Option[ResolvedStructField] =
    fields.find(_.name == name)
}

case class ResolvedStructField(
  parsed: MemberDefinition,
  name: String,
  structName: String,
  valueType: ResolvedType,
) extends ResolvedNode
