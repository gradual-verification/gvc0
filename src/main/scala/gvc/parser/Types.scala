package gvc.parser
import fastparse._

trait Types extends Lexer {
  def typeReference[_: P]: P[Type] =
    P("struct".!.? ~ identifier.! ~ typeModifier.rep)
      .map({
        case (hasStruct, name, modifiers) => {
          var typ = hasStruct match {
            case None => NamedType(Identifier(name))
            case Some(_) => NamedStructType(Identifier(name))
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