package gvteal.analyzer
import gvteal.parser._

case class ResolvedMethodDeclaration(
    parsed: MethodDefinition,
    returnType: ResolvedType,
    name: String,
    arguments: List[ResolvedVariable],
    precondition: Option[ResolvedExpression],
    postcondition: Option[ResolvedExpression],
    library: Boolean = false,
) extends ResolvedNode

case class ResolvedMethodDefinition(
    parsed: MethodDefinition,
    declaration: ResolvedMethodDeclaration,
    body: ResolvedBlock
) extends ResolvedNode {
  def name = declaration.name
}

case class ResolvedPredicateDeclaration(
    parsed: PredicateDefinition,
    name: String,
    arguments: List[ResolvedVariable]
) extends ResolvedNode

case class ResolvedPredicateDefinition(
    parsed: PredicateDefinition,
    declaration: ResolvedPredicateDeclaration,
    body: ResolvedExpression
) extends ResolvedNode {
  def name = declaration.name
}
