package gvc.parser
import fastparse._

trait Specifications extends Expressions {
  def specification[_: P]: P[Specification] =
    P(
      requiresSpecification |
      ensuresSpecification |
      loopInvariantSpecification |
      assertSpecification |
      foldSpecification |
      unfoldSpecification |
      pureSpecification
    ).opaque("<specification>")

  // Explicitly add space tokens here because whitespace handling is may be different
  // when invoked in a sub-parser
  def specifications[_: P]: P[Seq[Specification]] =
    P(space ~~ specification.rep ~~ space)
  
  def requiresSpecification[_: P]: P[RequiresSpecification] =
    P(span(kw("requires") ~/ expression ~ ";")).map({
      case (e, span) => RequiresSpecification(e, span)
    })

  def ensuresSpecification[_: P]: P[EnsuresSpecification] =
    P(span(kw("ensures") ~/ expression ~ ";")).map({
      case (e, span) => EnsuresSpecification(e, span)
    })
  
  def loopInvariantSpecification[_: P]: P[LoopInvariantSpecification] =
    P(span(kw("loop_invariant") ~/ expression ~/ ";")).map({
      case (e, span) => LoopInvariantSpecification(e, span)
    })
  
  def assertSpecification[_: P]: P[AssertSpecification] =
    P(span(kw("assert") ~/ expression ~/ ";")).map({
      case (e, span) => AssertSpecification(e, span)
    })

  def foldSpecification[_: P]: P[FoldSpecification] =
    P(span(kw("fold") ~/ identifier ~ "(" ~ expression.rep(sep = ",") ~ ")" ~ ";"))
      .map { case ((ident, args), span) => FoldSpecification(ident, args.toList, span) }
  
  def unfoldSpecification[_: P]: P[UnfoldSpecification] =
    P(span(kw("unfold") ~/ identifier ~ "(" ~ expression.rep(sep=",") ~ ")" ~ ";"))
      .map { case ((ident, args), span) => UnfoldSpecification(ident, args.toList, span) }

  def pureSpecification[_: P]: P[PureSpecification] =
    P(span(kw("pure") ~ ";")).map { case (_, span) => PureSpecification(span) }
  
  def annotations[_: P]: P[List[Specification]] =
    P(annotation.rep).map(a => a.flatten.toList)

  // used to differentiate between functions and methods
  def annotationsPure[_: P]: P[(List[Specification], Boolean)] =
    P(annotation.rep).map{ a =>
      val flat = a.flatten
      val isPure = flat.exists(_.isInstanceOf[PureSpecification])
      val rest = flat.filterNot(_.isInstanceOf[PureSpecification]).toList
      (rest, isPure)
    }

  def annotation[_: P]: P[Seq[Specification]] =
    P(singleLineAnnotation | multiLineAnnotation)
  def singleLineAnnotation[_: P]: P[Seq[Specification]] =
    P("//@"./.flatMapX(_ => new Parser(state.inSingleLineAnnotation()).specifications) ~~/ ("\n" | End))
  def multiLineAnnotation[_: P]: P[Seq[Specification]] =
    P("/*@"./.flatMapX(_ => new Parser(state.inAnnotation()).specifications) ~/ "@*/")
}