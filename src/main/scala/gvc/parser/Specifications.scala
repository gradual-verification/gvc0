package gvc.parser
import fastparse._

trait SpecExprifications extends Expressions {
  def specification[_: P]: P[SpecExprification] =
    P(
      requiresSpecExprification |
      ensuresSpecExprification |
      loopInvariantSpecExprification |
      assertSpecExprification |
      foldSpecExprification |
      unfoldSpecExprification
    ).opaque("<specification>")

  // Explicitly add space tokens here because whitespace handling is may be different
  // when invoked in a sub-parser
  def specifications[_: P]: P[Seq[SpecExprification]] =
    P(space ~~ specification.rep ~~ space)
  
  def requiresSpecExprification[_: P]: P[RequiresSpecExprification] =
    P(span(kw("requires") ~/ expression ~ ";")).map({
      case (e, span) => RequiresSpecExprification(e, span)
    })

  def ensuresSpecExprification[_: P]: P[EnsuresSpecExprification] =
    P(span(kw("ensures") ~/ expression ~ ";")).map({
      case (e, span) => EnsuresSpecExprification(e, span)
    })
  
  def loopInvariantSpecExprification[_: P]: P[LoopInvariantSpecExprification] =
    P(span(kw("loop_invariant") ~/ expression ~/ ";")).map({
      case (e, span) => LoopInvariantSpecExprification(e, span)
    })
  
  def assertSpecExprification[_: P]: P[AssertSpecExprification] =
    P(span(kw("assert") ~/ expression ~/ ";")).map({
      case (e, span) => AssertSpecExprification(e, span)
    })

  def foldSpecExprification[_: P]: P[FoldSpecExprification] =
    P(span(kw("fold") ~/ identifier ~ "(" ~ expression.rep(sep = ",") ~ ")" ~ ";"))
      .map { case ((ident, args), span) => FoldSpecExprification(ident, args.toList, span) }
  
  def unfoldSpecExprification[_: P]: P[UnfoldSpecExprification] =
    P(span(kw("unfold") ~/ identifier ~ "(" ~ expression.rep(sep=",") ~ ")" ~ ";"))
      .map { case ((ident, args), span) => UnfoldSpecExprification(ident, args.toList, span) }
  
  def annotations[_: P]: P[List[SpecExprification]] =
    P(annotation.rep).map(a => a.flatten.toList)

  def annotation[_: P]: P[Seq[SpecExprification]] =
    P(singleLineAnnotation | multiLineAnnotation)
  def singleLineAnnotation[_: P]: P[Seq[SpecExprification]] =
    P("//@"./.flatMapX(_ => new Parser(state.inSingleLineAnnotation()).specifications) ~~/ ("\n" | End))
  def multiLineAnnotation[_: P]: P[Seq[SpecExprification]] =
    P("/*@"./.flatMapX(_ => new Parser(state.inAnnotation()).specifications) ~/ "@*/")
}