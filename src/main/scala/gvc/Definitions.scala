package gvc
import fastparse._

trait Definitions extends Statements with Types {
  def definition[_: P]: P[AstDefinition] =
    P(structDefinition | typeDefinition | methodDefinition | useDeclaration)

  def structDefinition[_: P]: P[StructDefinition] =
    P("struct" ~ identifier.! ~ structFields.? ~ ";").map({
      case (id, fields) => StructDefinition(id, fields)
    })
  def structFields[_: P]: P[List[MemberDefinition]] =
    P("{" ~ structField.rep ~ "}").map(f => f.toList)
  def structField[_: P]: P[MemberDefinition] =
    P(typeReference ~ identifier.! ~ ";").map({
      case (typ, name) => MemberDefinition(name, typ)
    })
  
  def typeDefinition[_: P]: P[TypeDefinition] =
    P("typedef" ~ typeReference ~ identifier.! ~ ";").map({
      case (defType, defName) => TypeDefinition(defName, defType)
    })

  def methodDefinition[_: P]: P[MethodDefinition] =
    P(
      typeReference ~ identifier.! ~
      "(" ~ methodParameter.rep(0, ",") ~ ")" ~
      annotations ~
      (P(";").map(_ => None) | blockStatement.map(Some(_)))
    ).map({
      case (ret, name, args, annot, body) =>
        MethodDefinition(name, ret, args.toList, body, annot)
    })

  def methodParameter[_: P]: P[MemberDefinition] =
    P(typeReference ~ identifier.!).map({
      case (paramType, paramName) => MemberDefinition(paramName, paramType)
    })
  
  def useDeclaration[_: P]: P[UseDeclaration] = P("#use" ~/ usePath)
    .map(p => UseDeclaration(p.path, p.isInstanceOf[LibraryPath]))

  sealed trait UsePath {
    val path: StringExpression
  }
  case class LibraryPath(path: StringExpression) extends UsePath
  case class LocalPath(path: StringExpression) extends UsePath
  def usePath[_: P]: P[UsePath] =
    P(useLibraryPath | useLocalPath)
  def useLibraryPath[_: P]: P[LibraryPath] =
    P(library.!).map(raw => LibraryPath(StringExpression(raw, raw.substring(1, raw.length() - 1))))
  def useLocalPath[_: P]: P[LocalPath] =
    P(stringExpression).map(LocalPath(_))
}