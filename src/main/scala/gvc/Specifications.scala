package gvc
import fastparse._

trait Specifications extends Expressions {
  def specification[_: P]: P[Specification] =
    P(requiresSpecification |
      ensuresSpecification |
      loopInvariantSpecification |
      assertSpecification)
  
  def requiresSpecification[_: P]: P[RequiresSpecification] =
    P("requires" ~ expression ~ ";").map(RequiresSpecification(_))

  def ensuresSpecification[_: P]: P[EnsuresSpecification] =
    P("ensures" ~ expression ~ ";").map(EnsuresSpecification(_))
  
  def loopInvariantSpecification[_: P]: P[LoopInvariantSpecification] =
    P("loop_invariant" ~/ expression ~/ ";").map(LoopInvariantSpecification(_))
  
  def assertSpecification[_: P]: P[AssertSpecification] =
    P("assert" ~/ expression ~/ ";").map(AssertSpecification(_))
  
  def annotations[_: P]: P[List[Specification]] =
    P(annotation.rep).map(a => a.flatten.toList)

  def annotation[_: P]: P[Seq[Specification]] =
    P(singleLineAnnotation | multiLineAnnotation)
  def singleLineAnnotation[_: P]: P[Seq[Specification]] =
    P("//@" ~/ specification.rep ~/ "\n")
  def multiLineAnnotation[_: P]: P[Seq[Specification]] =
    P("/*@" ~/ specification.rep ~/ "@*/")
}