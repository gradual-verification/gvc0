package gvteal.analyzer

import gvteal.parser.UseDeclaration

import java.nio.file.Path

case class ResolvedUseDeclaration(
    parsed: UseDeclaration,
    name: String,
    isLibrary: Boolean,
    path: Option[Path],
    dependency: Option[ResolvedProgram]
) extends ResolvedNode
