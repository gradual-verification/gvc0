package gvc.analyzer
import gvc.parser._

case class ResolvedVariable(
  // Variable defs can come from args (MemberDefinitions) or
  // VariableStatements
  parsed: Node,
  name: String,
  valueType: ResolvedType,
) extends ResolvedNode
