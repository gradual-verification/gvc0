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
    P(binaryExpression ~ ("?" ~ expression ~ ":" ~ expression ~~ pos).?).map {
        case (a, None) => a
        case (a, Some((l, r, end))) => TernaryExpression(a, l, r, SourceSpan(a.span.start, end))
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
              result = BinaryExpression(result, binOp, rhs, SourceSpan(result.span.start, rhs.span.end))
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
    prefixWithPosition.rep ~ pos ~~ atomExpression ~ member.rep ~~ postfixWithPosition.?
  ).map({ case (pre, baseStart, expr, members, post) =>
    // TODO: Deref (*) is only allowed in L-Values
    val exp1 = members.foldLeft(expr)((e, item) => {
      val span = SourceSpan(baseStart, item.end)
      item match {
        case DottedMember(id, _) => MemberExpression(e, id, false, span)
        case PointerMember(id, _) => MemberExpression(e, id, true, span)
        case IndexMember(index, _) => IndexExpression(e, index, span)
      }
    })

    val exp2 = post.foldLeft(exp1) { (exp, posOp) => {
      posOp match {
        case (end, op) => IncrementExpression(exp, op, SourceSpan(exp.span.start, end))
      }
    }}

    pre.foldRight(exp2)((opPos, e) => opPos match {
      case (pos, op) => UnaryExpression(e, parsePrefixOp(op), SourceSpan(pos, e.span.end))
    })
  })

  def prefixWithPosition[_: P]: P[(SourcePosition, String)] = P(pos ~~ prefixOperator.!)

  def parsePrefixOp(op: String): UnaryOperator.Value = {
    import UnaryOperator._
    op match {
      case "*" => Deref
      case "-" => Negate
      case "!" => Not
      case "~" => BitwiseNot
    }
  }

  def postfixWithPosition[_: P]: P[(SourcePosition, IncrementOperator)] = P(postfixOperator.! ~~ pos)
    .map { case (op, pos) => (pos, op match {
      case "++" => IncrementOperator.Increment
      case "--" => IncrementOperator.Decrement
    }) }

  def atomExpression[_: P]: P[Expression] = P(
    parenExpression |
    stringExpression |
    characterExpression |
    hexNumberExpression |
    decimalNumberExpression |
    booleanExpression |
    nullExpression |
    resultExpression |
    lengthExpression |
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

  def resultExpression[_: P]: P[ResultExpression] = P(span(kw("\\result")))
    .map({ case (_, span) => ResultExpression(span) })

  def lengthExpression[_: P]: P[LengthExpression] = P(span(kw("\\length") ~ "(" ~ expression ~ ")"))
    .map { case (expr, span) => LengthExpression(expr, span) }

  def parseString(raw: String): String = {
    // TODO: Replace this with a better solution that doesn't search the string
    // multiple times
    raw.substring(1, raw.length() - 1)
      .replace("\\n", "\n")
      .replace("\\t", "\t")
      .replace("\\v", "\u000b")
      .replace("\\b", "\b")
      .replace("\\r", "\r")
      .replace("\\f", "\f")
      .replace("\\a", "\u0007")
      .replace("\\\"", "\"")
      .replace("\\'", "'")
      .replace("\\\\", "\\")
      .replace("\\0", "\u0000")
  }

  def parseChar(raw: String): Char = {
    parseString(raw)(0)
  }

  def allocExpression[_: P]: P[AllocExpression] =
    P(span(kw("alloc") ~ "(" ~ typeReference ~ ")")).map({
      case (valueType, span) => AllocExpression(valueType, span)
    })
  
  def allocArrayExpression[_: P]: P[AllocArrayExpression] =
    P(span(kw("alloc_array") ~ "(" ~ typeReference ~ "," ~ expression ~ ")"))
      .map({ case ((valueType, length), span) => AllocArrayExpression(valueType, length, span) })

  def invokeExpression[_: P]: P[InvokeExpression] =
    P(span(identifier ~ "(" ~ expression.rep(0, ",") ~ ")"))
      .map({ case ((id, args), span) => InvokeExpression(id, args.toList, span) })

  def variableExpression[_: P]: P[VariableExpression] = P(identifier)
    .map(id => VariableExpression(id, id.span))

  sealed trait Member {
    val end: SourcePosition
  }
  case class DottedMember(field: Identifier, end: SourcePosition) extends Member
  case class PointerMember(field: Identifier, end: SourcePosition) extends Member
  case class IndexMember(index: Expression, end: SourcePosition) extends Member

  def member[_: P]: P[Member] = P(dottedMember | pointerMember | indexMember)
  def dottedMember[_: P]: P[DottedMember] = P("." ~ identifier ~~ pos)
    .map({ case (e, pos) => DottedMember(e, pos) })
  def pointerMember[_: P]: P[PointerMember] = P("->" ~ identifier ~~ pos)
    .map({ case (e, pos) => PointerMember(e, pos) })
  def indexMember[_: P]: P[IndexMember] = P("[" ~ expression ~ "]" ~~ pos)
    .map({ case (e, pos) => IndexMember(e, pos) })
}