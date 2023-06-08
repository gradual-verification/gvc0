package gvteal.analyzer
import gvteal.parser._

case class ResolvedVariable(
  // Variable defs can come from args (MemberDefinitions) or
  // VariableStatements
  parsed: Node,
  name: String,
  valueType: ResolvedType,
) extends ResolvedNode
