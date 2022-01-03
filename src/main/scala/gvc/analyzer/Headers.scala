package gvc.analyzer

import gvc.parser.UseDeclaration

case class ResolvedUseDeclaration(
    parsed: UseDeclaration,
    name: String,
    isLibrary: Boolean
) extends ResolvedNode
