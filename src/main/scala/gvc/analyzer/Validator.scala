package gvc.analyzer

import gvc.parser.Definition

object Validator {
  def validateParsed(defn: List[Definition], errors: ErrorSink): Option[ResolvedProgram] = {
    val result = Resolver.resolveProgram(defn, errors)
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