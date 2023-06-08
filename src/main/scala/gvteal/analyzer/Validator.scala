package gvteal.analyzer

import gvteal.parser.Definition

object Validator {
  def validateParsed(
      defn: List[Definition],
      librarySearchPaths: List[String],
      errors: ErrorSink
  ): Option[ResolvedProgram] = {
    val result = Resolver.resolveProgram(defn, librarySearchPaths, errors)
    (if (errors.errors.isEmpty) Some(result) else None)
      .filter(validate(_, errors))
  }

  def validate(program: ResolvedProgram, errors: ErrorSink): Boolean = {
    TypeChecker.check(program, errors)
    errors.errors.isEmpty && {
      AssignmentValidator.validate(program, errors)
      ReturnValidator.validate(program, errors)
      SpecificationValidator.validate(program, errors)
      ImplementationValidator.validate(program, errors)
      errors.errors.isEmpty
    }
  }
}
