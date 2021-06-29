package gvc.parser
import fastparse._

trait Specifications extends Expressions {
  def specification[_: P]: P[Specification] =
    P(
      requiresSpecification |
      ensuresSpecification |
      loopInvariantSpecification |
      assertSpecification
    ).opaque("<specification>")

  // Explicitly add space tokens here because whitespace handling is may be different
  // when invoked in a sub-parser
  def specifications[_: P]: P[Seq[Specification]] =
    P(space ~~ specification.rep ~~ space)
  
  def requiresSpecification[_: P]: P[RequiresSpecification] =
    P(kw("requires") ~/ expression ~ ";").map(RequiresSpecification(_))

  def ensuresSpecification[_: P]: P[EnsuresSpecification] =
    P(kw("ensures") ~/ expression ~ ";").map(EnsuresSpecification(_))
  
  def loopInvariantSpecification[_: P]: P[LoopInvariantSpecification] =
    P(kw("loop_invariant") ~/ expression ~/ ";").map(LoopInvariantSpecification(_))
  
  def assertSpecification[_: P]: P[AssertSpecification] =
    P(kw("assert") ~/ expression ~/ ";").map(AssertSpecification(_))
  
  def annotations[_: P]: P[List[Specification]] =
    P(annotation.rep).map(a => a.flatten.toList)

  def annotation[_: P]: P[Seq[Specification]] =
    P(singleLineAnnotation | multiLineAnnotation)
  def singleLineAnnotation[_: P]: P[Seq[Specification]] =
    P("//@"./.flatMapX(_ => new Parser(state.inSingleLineAnnotation()).specifications) ~~/ ("\n" | End))
  def multiLineAnnotation[_: P]: P[Seq[Specification]] =
    P("/*@"./.flatMapX(_ => new Parser(state.inAnnotation()).specifications) ~/ "@*/")
}