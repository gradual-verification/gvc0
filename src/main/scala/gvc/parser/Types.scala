package gvc.parser
import fastparse._

trait Types extends Lexer {
  def typeReference[_: P]: P[AstType] =
    P("struct".!.? ~ identifier.! ~ typeModifier.rep)
      .map({
        case (hasStruct, id, modifiers) => {
          var typ = hasStruct match {
            case None => NamedType(id)
            case Some(_) => NamedStructType(id)
          }

          modifiers.foldLeft(typ)((t, mod) => {
            mod match {
              case PointerModifier => PointerType(t)
              case ArrayModifier => ArrayType(t)
            }
          })
        }
      })

  trait TypeModifier
  case object PointerModifier extends TypeModifier
  case object ArrayModifier extends TypeModifier
  def typeModifier[_: P]: P[TypeModifier] =
      P(pointerModifier | arrayModifier)
  def pointerModifier[_: P]: P[TypeModifier] =
      P("*").map(_ => PointerModifier)
  def arrayModifier[_: P]: P[TypeModifier] =
      P("[" ~ "]").map(_ => ArrayModifier)
}