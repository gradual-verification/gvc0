package gvc.analyzer

import gvc.parser.UseDeclaration

import java.nio.file.Path

case class ResolvedUseDeclaration(
    parsed: UseDeclaration,
    name: String,
    isLibrary: Boolean,
    filePath: Path
) extends ResolvedNode
