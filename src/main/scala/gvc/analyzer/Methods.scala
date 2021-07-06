package gvc.analyzer
import gvc.parser._

case class ResolvedMethodDeclaration(
  parsed: MethodDefinition,
  returnType: ResolvedType,
  name: String,
  arguments: List[ResolvedVariable],
  precondition: Option[ResolvedExpression],
  postcondition: Option[ResolvedExpression]
)

case class ResolvedMethodDefinition(
  parsed: MethodDefinition,
  declaration: ResolvedMethodDeclaration,
  body: ResolvedBlock
) {
  def name = declaration.name
}