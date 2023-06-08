package gvteal.parser
import fastparse._

trait Types extends Lexer {
  def typeReference[_: P]: P[Type] =
    P(pos ~~ kw("struct").!.? ~ identifier ~ typeModifier.rep)
      .map({
        case (start, hasStruct, id, modifiers) => {
          val baseSpan = SourceSpan(start, id.span.end)
          val baseType = hasStruct match {
            case None => NamedType(id, baseSpan)
            case Some(_) => NamedStructType(id, baseSpan)
          }

          modifiers.foldLeft(baseType)((t, mod) => {
            val span = SourceSpan(start, mod.end)
            mod match {
              case _: PointerModifier => PointerType(t, span)
              case _: ArrayModifier => ArrayType(t, span)
            }
          })
        }
      })

  trait TypeModifier {
    val end: SourcePosition
  }
  case class PointerModifier(end: SourcePosition) extends TypeModifier
  case class ArrayModifier(end: SourcePosition) extends TypeModifier
  def typeModifier[_: P]: P[TypeModifier] =
      P(pointerModifier | arrayModifier)
  def pointerModifier[_: P]: P[TypeModifier] =
      P("*" ~~ pos).map(PointerModifier(_))
  def arrayModifier[_: P]: P[TypeModifier] =
      P("[" ~ "]" ~~ pos).map(ArrayModifier(_))
}