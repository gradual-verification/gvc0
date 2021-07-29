package gvc.analyzer
import gvc.parser._

case class ResolvedMethodDeclaration(
  parsed: MethodDefinition,
  returnType: ResolvedType,
  name: String,
  arguments: List[ResolvedVariable],
  precondition: Option[ResolvedExpression],
  postcondition: Option[ResolvedExpression]
) extends ResolvedNode

case class ResolvedMethodDefinition(
  parsed: MethodDefinition,
  declaration: ResolvedMethodDeclaration,
  body: ResolvedBlock
) extends ResolvedNode {
  def name = declaration.name
}

case class ResolvedPredicateDefinition(
  parsed: MethodDefinition,
  declaration: ResolvedMethodDeclaration,
  body: ResolvedExpression
) extends ResolvedNode