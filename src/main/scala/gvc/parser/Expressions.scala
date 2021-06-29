package gvc.parser
import fastparse._

trait Expressions extends Types {
  import BinaryOperator._

  val operators: Map[String, (Int, BinaryOperator)] = Map(
    "||" -> (1,  LogicalOr),
    "&&" -> (2,  LogicalAnd),
    "|"  -> (3,  BitwiseOr),
    "^"  -> (4,  BitwiseXor),
    "&"  -> (5,  BitwiseAnd),
    "==" -> (6,  Equal),
    "!=" -> (6,  NotEqual),
    "<"  -> (7,  Less),
    "<=" -> (7,  LessEqual),
    ">=" -> (7,  GreaterEqual),
    ">"  -> (7,  Greater),
    "<<" -> (8,  ShiftLeft),
    ">>" -> (8,  ShiftRight),
    "+"  -> (9,  Add),
    "-"  -> (9,  Subtract),
    "*"  -> (10,  Multiply),
    "/"  -> (10,  Divide),
    "%"  -> (10,  Modulus),
  )

  def expression[_: P]: P[Expression] =
    P(binaryExpression ~ ("?" ~ expression ~ ":" ~ expression).?).map {
        case (a, None) => a
        case (a, Some((l, r))) => TernaryExpression(a, l, r)
      }

  def binaryExpression[_: P]: P[Expression] =
      P(basicExpression ~ (binaryOperator.! ~ basicExpression).rep).map {
        case (cur, rest) => parseOpPrecedence(cur, rest)
      }

  def parseOpPrecedence(current: Expression, rest: Seq[(String, Expression)]): Expression = {
    // Operator precedence climbing algorithm
    // Based on https://github.com/databricks/sjsonnet/blob/master/sjsonnet/src/sjsonnet/Parser.scala#L156-L200
    var remaining = rest
    def climb(minPrec: Int, current: Expression): Expression = {
      var result = current
      while (
        remaining.headOption match {
          case None => false
          case Some((op, next)) =>
            val (prec, binOp) = operators(op)
            if (prec < minPrec) false
            else {
              remaining = remaining.tail
              val rhs = climb(prec + 1, next)
              result = BinaryExpression(result, binOp, rhs)
              true
            }
        }
      )()

      result
    }

    climb(0, current)
  }

  // Expressions with concrete start and end tokens
  def basicExpression[_: P]: P[Expression] = P(
    prefixOperator.!.rep ~ atomExpression ~ member.rep
  ).map({ case (pre, expr, members) =>
    // TODO: Deref (*) is only allowed in L-Values
    var member = members.foldLeft(expr)((e, item) => {
      item match {
        case DottedMember(id) => MemberExpression(e, id, false)
        case PointerMember(id) => MemberExpression(e, id, true)
        case IndexMember(index) => IndexExpression(e, index)
      }
    })

    pre.foldLeft(member)((e, op) => UnaryExpression(e, parsePrefixOp(op)))
  })

  def parsePrefixOp(op: String): UnaryOperator.Value = {
    import UnaryOperator._
    op match {
      case "*" => Deref
      case "-" => Negate
      case "!" => Not
      case "~" => BitwiseNot
    }
  }

  def atomExpression[_: P]: P[Expression] = P(
    parenExpression |
    stringExpression |
    characterExpression |
    hexNumberExpression |
    decimalNumberExpression |
    booleanExpression |
    nullExpression |
    allocExpression |
    allocArrayExpression |
    invokeExpression |
    variableExpression
  )

  def parenExpression[_: P]: P[Expression] = P("(" ~ expression ~ ")")

  def stringExpression[_: P]: P[StringExpression] = P(span(string.!))
    .map({ case(raw, span) => StringExpression(raw, parseString(raw), span) })

  def libraryExpression[_: P]: P[StringExpression] = P(span(library.!))
    .map({ case (raw, span) => StringExpression(raw, parseString(raw), span) })

  def characterExpression[_: P]: P[CharacterExpression] = P(span(character.!))
    .map({ case (raw, span) => CharacterExpression(raw, parseChar(raw), span) })

  def hexNumberExpression[_: P]: P[IntegerExpression] = P(span(hexNumber.!))
    // Trim the 0x prefix before parsing to Int
    .map({ case (raw, span) => IntegerExpression(raw, Integer.parseInt(raw.substring(2), 16), span) })
  
  def decimalNumberExpression[_: P]: P[IntegerExpression] = P(span(decimalNumber.!))
    .map({ case (raw, span) => IntegerExpression(raw, raw.toInt, span) })

  def booleanExpression[_: P]: P[BooleanExpression] = P(span(kw(StringIn("true", "false")).!))
    .map({ case (raw, span) => BooleanExpression(raw, raw match {
      case "true" => true
      case "false" => false
    }, span) })

  def nullExpression[_: P] : P[NullExpression] = P(span(kw("NULL").!))
    .map({ case (raw, span) => NullExpression(raw, null, span) })

  def parseString(raw: String): String = {
    // TODO: Replace this with a better solution that doesn't search the string
    // multiple times
    raw.substring(1, raw.length() - 1)
      .replace("\\n", "\n")
      .replace("\\t", "\t")
      .replace("\\v", "\13")
      .replace("\\b", "\b")
      .replace("\\r", "\r")
      .replace("\\f", "\f")
      .replace("\\a", "\07")
      .replace("\\\"", "\"")
      .replace("\\'", "'")
      .replace("\\\\", "\\")
      .replace("\\0", "\0")
  }

  def parseChar(raw: String): Char = {
    parseString(raw)(0)
  }

  def allocExpression[_: P]: P[AllocExpression] =
    P(kw("alloc") ~ "(" ~ typeReference ~ ")").map(AllocExpression(_))
  
  def allocArrayExpression[_: P]: P[AllocArrayExpression] =
    P(kw("alloc_array") ~ "(" ~ typeReference ~ "," ~ expression ~ ")")
      .map({ case (typeRef, length) => AllocArrayExpression(typeRef, length) })

  def invokeExpression[_: P]: P[InvokeExpression] =
    P(identifier ~ "(" ~ expression.rep(0, ",") ~ ")")
      .map({ case (id, args) => InvokeExpression(id, args.toList) })

  def variableExpression[_: P]: P[VariableExpression] = P(identifier)
    .map(VariableExpression(_))

  sealed trait Member
  case class DottedMember(field: Identifier) extends Member
  case class PointerMember(field: Identifier) extends Member
  case class IndexMember(index: Expression) extends Member

  def member[_: P]: P[Member] = P(dottedMember | pointerMember | indexMember)
  def dottedMember[_: P]: P[DottedMember] = P("." ~ identifier)
    .map(DottedMember(_))
  def pointerMember[_: P]: P[PointerMember] = P("->" ~ identifier)
    .map(PointerMember(_))
  def indexMember[_: P]: P[IndexMember] = P("[" ~ expression ~ "]")
    .map(IndexMember(_))
}