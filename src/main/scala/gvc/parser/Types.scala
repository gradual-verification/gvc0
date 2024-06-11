package gvc.parser
import fastparse._

trait Types extends Lexer {
  def typeReference[_: P]: P[Type] =
    P(pos ~~ structReference ~ typeModifier.rep) 
      .map({
        case (start, (hasStruct, id), modifiers) => {
          val baseSpan = SourceSpan(start, id.span.end)
          val baseType = if (hasStruct) {
            NamedStructType(id, baseSpan)
          } else { NamedType(id, baseSpan) }

          modifiers.foldLeft(baseType)((t, mod) => {
            val span = SourceSpan(start, mod.end)
            mod match { 
              case _: PointerModifier => PointerType(t, span)
              case _: ArrayModifier => ArrayType(t, span)
            }
          })
        }      })
  
  //If struct, cannot be followed by int, void, bool, or char, must be identifier.
  //If not struct, can be int, void, bool, char or identifier.
  def structReference[_: P]: P[(Boolean, Identifier)] = 
    P(kw("struct").!.?.flatMap({
      case None => typeIdentifier.map({
        case(id) => (false, id)
      })
      case Some(_) => identifier.map({
        case(id) => (true, id)
      })
    }))

  def typeIdentifier[_: P]: P[Identifier] = 
    P(span(!typeKeywords ~ ident.!)).map({
      case(id, span) => Identifier(id ,span)
    })

  def typeKeywords[_: P] = {
    StringIn("while", "if", "for", "assert", "NULL", "else", "true", 
    "false", "struct", "alloc", "alloc_array", "typedef", "error", "return") ~~ 
    !CharIn("A-Za-z0-9_")
  }
  
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