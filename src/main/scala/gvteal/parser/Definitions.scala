package gvteal.parser
import fastparse._

trait Definitions extends Statements with Types {
  def definition[_: P]: P[Seq[Definition]] =
    P(
      structDefinition.map(Seq(_)) |
      typeDefinition.map(Seq(_)) |
      methodDefinition.map(Seq(_)) |
      useDeclaration.map(Seq(_)) |
      importDeclaration.map(Seq(_)) |
      predicateAnnotation
    )

  def structDefinition[_: P]: P[StructDefinition] =
    P(span(kw("struct") ~ identifier ~ structFields.? ~ ";")).map({
      case ((id, fields), span) => StructDefinition(id, fields, span)
    })
  def structFields[_: P]: P[List[MemberDefinition]] =
    P("{" ~ structField.rep ~ "}").map(f => f.toList)
  def structField[_: P]: P[MemberDefinition] =
    P(typeReference ~ identifier ~ ";" ~~ pos).map({
      case (typ, id, end) => MemberDefinition(id, typ, SourceSpan(typ.span.start, end))
    })
  
  def typeDefinition[_: P]: P[TypeDefinition] =
    P(span(kw("typedef") ~ typeReference ~ identifier ~ ";")).map({
      case ((defType, id), span) => TypeDefinition(id, defType, span)
    })

  def methodDefinition[_: P]: P[MethodDefinition] =
    P(
      typeReference ~ identifier ~ "(" ~ methodParameter.rep(0, ",") ~ ")" ~
      annotations ~
      (P(";").map(_ => None) | blockStatement.map(Some(_))) ~~
      pos
    ).map({
      case (ret, id, args, annot, body, end) =>
        MethodDefinition(id, ret, args.toList, body, annot, SourceSpan(ret.span.start, end))
    })

  def methodParameter[_: P]: P[MemberDefinition] =
    P(typeReference ~ identifier).map({
      case (paramType, id) => MemberDefinition(id, paramType, SourceSpan(paramType.span.start, id.span.end))
    })
  
  // PyTEAL imports for the head of a file
  // TODO: Python imports aren't as simple as `use`, instead make use of `from ... import`; 
  // we need to define both an `importPath` and an `importFnc` 
  // def importDeclaration[_: P]: P[ImportDeclaration] =
  //   P("from" ~ " " importPath ~ " " ~ "import" ~ " " ~ importFnc | ("import" ~/ importPath))
  //     .map({
  //       case(start, p) => ImportDeclaration(p.path, p.isInstanceOf[LibraryPath], SourceSpan(start, p.path.span.end))
  //   }) 
  
  // sealed trait ImportPath {
  //   val path: StringExpression
  // }

  // sealed trait ImportFnc {
  //   val fnc: StringExpression
  // }

  // def importPath[_: P]: P[ImportPath] = 
  //   P(useLibraryPath | useLocalPath)
  
  // def importFnc[_: P]: P[ImportFnc] = 
  //   P(importLibraryFnc)
  
  // case class LibraryFnc(function: StringExpression) extends ImportPath

  // TODO: Figure out what a `libraryfunction` looks like
  // def importLibraryFnc[_: P]: P[LibraryFnc] = 
  //   P(span(library.!)).map({
  //     case (raw, span) => LibraryFnc(StringExpression(raw, raw.substring(1, raw.length() - 1), span))
  //   })

  def importDeclaration[_: P]: P[Definition] =
    P(importSimple | importFrom)
  
  def importSimple[_: P]: P[ImportSimple] = P(pos ~~ kw("import") ~/ importPath)
    .map({
      case(start, p) => ImportSimple(p, SourceSpan(start, p.span.end))
  })
  
  def importPath[_: P]: P[StringExpression] = 
    P(identifier.rep(1, sep=".")).map({ identifiers =>
      val raw = identifiers.map(_.name).mkString(".")
      val start = identifiers.head.span.start
      val end = identifiers.last.span.end
      StringExpression(raw, raw, SourceSpan(start, end))
    })

  def importFrom[_: P]: P[Definition] =
    P((Index ~~ kw("from") ~/ identifier ~ kw("import") ~/ ("*".!.map(_ => Right(Nil)) | identifier.rep(sep = ",").map(Left(_))) ~~ Index).map {
      // from vote import approval_program, clear_state_program
      case (start, name, Left(functions), end) => ImportFrom(StringExpression(name.name, name.name, name.span), functions.map(f => f.name).toList, SourceSpan(name.span.start, name.span.end))
      // from pyteal import *
      case (start, name, Right(_), end) => ImportFromAll(StringExpression(name.name, name.name, name.span), SourceSpan(name.span.start, name.span.end))
    })

  def useDeclaration[_: P]: P[UseDeclaration] = P(pos ~~ kw("#use") ~/ usePath)
    .map({
      case(start, p) => UseDeclaration(p.path, p.isInstanceOf[LibraryPath], SourceSpan(start, p.path.span.end))
    })

  sealed trait UsePath {
    val path: StringExpression
  }
  case class LibraryPath(path: StringExpression) extends UsePath
  case class LocalPath(path: StringExpression) extends UsePath
  def usePath[_: P]: P[UsePath] = 
    P(useLibraryPath | useLocalPath)
  def useLibraryPath[_: P]: P[LibraryPath] =
    P(span(library.!)).map({
      case (raw, span) => LibraryPath(StringExpression(raw, raw.substring(1, raw.length() - 1), span))
    })
  def useLocalPath[_: P]: P[LocalPath] =
    P(stringExpression).map(LocalPath(_))

  def predicateAnnotation[_: P]: P[Seq[PredicateDefinition]] =
    P(singleLinePredicateAnnotation | multiLinePredicateAnnotation)

  def singleLinePredicateAnnotation[_: P]: P[Seq[PredicateDefinition]] =
    P("#@"./.flatMapX(_ => new Parser(state.inSingleLineAnnotation()).predicateDefinitions) ~~/ ("\n" | End))
  def multiLinePredicateAnnotation[_: P]: P[Seq[PredicateDefinition]] =
    P("\"\"\"@"./.flatMapX(_ => new Parser(state.inAnnotation()).predicateDefinitions) ~/ "@\"\"\"")

  def predicateDefinitions[_: P]: P[Seq[PredicateDefinition]] =
    P(space ~~ predicateDefinition.rep ~~ space)

  def predicateDefinition[_: P]: P[PredicateDefinition] =
    P(span("predicate" ~ identifier ~ "(" ~ methodParameter.rep(sep = ",") ~ ")" ~/ (predicateBody | emptyPredicateBody)))
    .map { case ((ident, args, body), span) => PredicateDefinition(ident, args.toList, body, span) }
  
  def emptyPredicateBody[_: P]: P[Option[Expression]] = P(";").map(_ => None)

  def predicateBody[_: P]: P[Option[Expression]] =
    P("=" ~/ expression ~/ ";").map(Some(_))
}
