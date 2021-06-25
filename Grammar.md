# Grammar

## Whitespace

Whitespace is a regular space, horizontal and vertical tab newline, formfeed and comments (C0 Reference). Multi-line comments can be nested. Whitespace may come between any tokens, except the sequences defined in the Lexical Tokens section.

```
whitespace ::= whitespaceAtom+

whitespaceAtom ::= (space) | (horizontal tab) |
                  (vertical tab) | (new line) | (formfeed) |
                  singleLineComment | multiLineComment

singleLineComment ::= // [^\n]* \n

multiLineComment ::=  /* (multiLineComment | (any char))* */
```

## Lexical Tokens

The sequences defined in this section may not contain whitespace between the tokens.

**Divergence**
 * `normalChar` excludes `\` (this removes an ambiguity in the original grammar)
```

identifier := [A-Za-z_] [A-Za-z0-9_]*

decimalNumber := 0 | [1-9] [0-9]*

hexNumber := 0 [xX] [0-9a-fA-F]+

string := " stringChar* "

chararacter := ' charChar '

library := < libraryChar* >

stringChar := normalChar | escape

charChar := normalChar | escape | " | \0

libraryChar := (not control char and not >)

normalChar := (not control char, not ", and not \)

escape := \ [ntvbrfa"']
```

## Operators

**Diverges from reference**: `.`, `->`, `?`, and `:` are not defined as binary operators since they have difference semantics from the other binary operators

```
prefixOperator := ! | ~ | - | *

postfixOperator := -- | ++

binaryOperator := * | / | % | + | - | << | >> |
                  < | <= | >= | > | == | != |
                  & | ^ | | | && | ||

assignmentOperator := = | += | -= | *= | /= | %= |
                      <<= | >>= | &= | ^= | |=
```

## Types

**Divergence from reference:**
 * Reserved names are parsed as normal identifiers

```
typeReference ::= [ struct ] identifier typeModifier*

typeModifier ::= * | [ ]
```

## Expressions

```
expression ::= binaryExpression [? expression : expression]

binaryExpression ::= basicExpression (binaryOperator basicExpression)*

basicExpression ::= prefixOperator* atomExpression member*

atomExpression ::=
  | parenExpression
  | stringExpression
  | characterExpression
  | hexNumberExpression
  | decimalNumberExpression
  | booleanExpression
  | nullExpression
  | allocExpression
  | allocArrayExpression
  | invokeExpression
  | variableExpression

parenExpression ::= ( expression )

stringExpression ::= string
libraryExpression ::= library
characterExpression ::= character
hexNumberExpression ::= hexNumber
decimalNumberExpression ::= decimalNumber
booleanExpression ::= true | false
nullExpression ::= NULL

allocExpression ::= alloc ( type )

allocArrayExpression ::= alloc_array ( type , expression )

invokeExpression ::= identifier ( expression (, expression)* )

variableExpression ::= identifier

member ::= dottedMember | pointerMember | indexMember
dottedMember ::= . identifier
pointerMember ::= -> identifier
indexMember ::= [ expression ]
```

## Statements

**Divergence from reference:**
 * L-Values are parsed as expressions, which means that invalid statements can be successfully parsed where a complex expression is used where an L-Value is required.
 * Parsing postfix operations at this level violates the operator precedence, but since the LHS must be an L-Value, operators (except for `*`) will not be used in the LHS if it is well-formed. This means that only the precedence of the `*` operator relative to the postfix operators matters for well-formed code.

```
statement ::= blockStatement |
              ifStatement |
              whileStatement |
              forStatement |
              returnStatement |
              assertStatement |
              errorStatement |
              simpleStatement ;

blockStatement ::= { statement* }

ifStatement ::= if ( expression ) statement [else statement]

whileStatement ::= while ( expression ) statement

forStatement ::= for ( simpleStatement ; expression ; simpleStatement ) statement

returnStatement ::= return [expression] ;

assertStatement ::= assert ( expression ) ;

errorStatement ::= error ( expression ) ;

simpleStatement ::= variableStatement |
                    expressionStatement
variableStatement ::= typeReference identifier [= expression]
expressionStatement ::= expression [postfixOperator | (assignmentOperator expression)]
```

## Definitions

**Divergence from reference**
 * Declarations are parsed as definitions with no body, not as a separate construct

```
definition ::= structDefinition |
               typeDefinition |
               methodDefinition |
               useDeclaration

structDefinition ::= struct identifier [structFields] ;
structFields ::= { structField* }
structField ::= typeReference identifier ;

typeDefinition ::= typedef typeReference identifier ;

methodDefinition ::= typeReference identifier ( [methodParameter (, methodParameter)*] ) (blockStatement | ;)

methodParameter ::= typeReference identifier

useDeclaration ::= #use (libraryExpression | stringExpression)
```