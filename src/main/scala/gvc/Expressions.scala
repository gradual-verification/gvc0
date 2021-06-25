package gvc
import fastparse._

trait Expressions extends Types {
  val operators: Map[String, (Int, BinaryOp.BinaryOp)] = Map(
    "||" -> (1, BinaryOp.LogicalOr),
    "&&" -> (2, BinaryOp.LogicalAnd),
    "|" -> (3, BinaryOp.BitwiseOr),
    "^" -> (4, BinaryOp.BitwiseXor),
    "&" -> (5, BinaryOp.BitwiseAnd),
    "==" -> (6, BinaryOp.Equal),
    "!=" -> (6, BinaryOp.NotEqual),
    "<" -> (7, BinaryOp.Less),
    "<=" -> (7, BinaryOp.LessEqual),
    ">=" -> (7, BinaryOp.GreaterEqual),
    ">" -> (7, BinaryOp.Greater),
    "<<" -> (8, BinaryOp.ShiftLeft),
    ">>" -> (8, BinaryOp.ShiftRight),
    "+" -> (9, BinaryOp.Add),
    "-" -> (9, BinaryOp.Subtract),
    "*" -> (10, BinaryOp.Multiply),
    "/" -> (10, BinaryOp.Divide),
    "%" -> (10, BinaryOp.Modulus),
  )

  def expression[_: P]: P[AstExpression] =
    P(binaryExpression ~ ("?" ~ expression ~ ":" ~ expression).?).map {
        case (a, None) => a
        case (a, Some((l, r))) => TernaryOperation(a, l, r)
      }

  def binaryExpression[_: P]: P[AstExpression] =
      P(basicExpression ~ (binaryOperator.! ~ basicExpression).rep).map {
        case (cur, rest) => parseOpPrecedence(cur, rest)
      }

  def parseOpPrecedence(current: AstExpression, rest: Seq[(String, AstExpression)]): AstExpression = {
    // Operator precedence climbing algorithm
    // Based on https://github.com/databricks/sjsonnet/blob/master/sjsonnet/src/sjsonnet/Parser.scala#L156-L200
    var remaining = rest
    def climb(minPrec: Int, current: AstExpression): AstExpression = {
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
              result = BinaryExpression(result, rhs, binOp)
              true
            }
        }
      )()

      result
    }

    climb(0, current)
  }

  // Expressions with concrete start and end tokens
  def basicExpression[_: P]: P[AstExpression] = P(
    prefixOperator.!.rep ~ atomExpression ~ member.rep
  ).map({ case (pre, expr, members) =>
    // TODO: Deref (*) is only allowed in L-Values
    var member = members.foldLeft(expr)((e, item) => {
      item match {
        case DottedMember(id) => MemberExpression(e, id)
        case PointerMember(id) => MemberDerefExpression(e, id)
        case IndexMember(index) => IndexExpression(e, index)
      }
    })

    pre.foldLeft(member)((e, op) => UnaryExpression(e, parsePrefixOp(op)))
  })

  def parsePrefixOp(op: String): UnaryOp.UnaryOp = {
    op match {
      case "*" => UnaryOp.Deref
      case "-" => UnaryOp.Negate
      case "!" => UnaryOp.Not
      case "~" => UnaryOp.BitwiseNot
    }
  }

  def atomExpression[_: P]: P[AstExpression] = P(
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

  def parenExpression[_: P]: P[AstExpression] = P("(" ~ expression ~ ")")

  def stringExpression[_: P]: P[StringExpression] = P(string.!)
    .map(raw => StringExpression(raw, parseString(raw)))

  def libraryExpression[_: P]: P[StringExpression] = P(library.!)
    .map(raw => StringExpression(raw, parseString(raw)))

  def characterExpression[_: P]: P[CharacterExpression] = P(character.!)
    .map(raw => CharacterExpression(raw, parseChar(raw)))

  def hexNumberExpression[_: P]: P[IntegerExpression] = P(hexNumber.!)
    // Trim the 0x prefix before parsing to Int
    .map(raw => IntegerExpression(raw, Integer.parseInt(raw.substring(2), 16)))
  
  def decimalNumberExpression[_: P]: P[IntegerExpression] = P(decimalNumber.!)
    .map(raw => IntegerExpression(raw, raw.toInt))

  def booleanExpression[_: P]: P[BooleanExpression] = P(StringIn("true", "false").!)
    .map(raw => BooleanExpression(raw, raw match {
      case "true" => true
      case "false" => false
    }))

  def nullExpression[_: P] : P[NullExpression] = P("NULL".!)
    .map(raw => NullExpression(raw, null))

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
    P("alloc" ~ "(" ~ typeReference ~ ")").map(AllocExpression(_))
  
  def allocArrayExpression[_: P]: P[AllocArrayExpression] =
    P("alloc_array" ~ "(" ~ typeReference ~ "," ~ expression ~ ")")
      .map({ case (typeRef, length) => AllocArrayExpression(typeRef, length) })

  def invokeExpression[_: P]: P[InvokeExpression] =
    P(identifier.! ~ "(" ~ expression.rep(0, ",") ~ ")")
      .map({ case (id, args) => InvokeExpression(id, args.toList) })

  def variableExpression[_: P]: P[VariableExpression] = P(identifier.!)
    .map(VariableExpression(_))

  sealed trait Member
  case class DottedMember(field: String) extends Member
  case class PointerMember(field: String) extends Member
  case class IndexMember(index: AstExpression) extends Member

  def member[_: P]: P[Member] = P(dottedMember | pointerMember | indexMember)
  def dottedMember[_: P]: P[DottedMember] = P("." ~ identifier.!)
    .map(DottedMember(_))
  def pointerMember[_: P]: P[PointerMember] = P("->" ~ identifier.!)
    .map(PointerMember(_))
  def indexMember[_: P]: P[IndexMember] = P("[" ~ expression ~ "]")
    .map(IndexMember(_))
}