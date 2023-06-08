# Parser

The parser in GVC0 converts source code into an unresolved parse AST. It is written using the [FastParse](https://com-lihaoyi.github.io/fastparse/) library.

The parser should only be used through the interface defined in the `Parser` object. This handles setting up a parse state automatically.

# Code Structure

The parser code is contained in `/src/main/scala/gvteal/parser`. Parser code is separated into several files:

 * `AST`: AST data structure definitions
 * `ParserState`: Immutable data structure that contains line indices and parser state data, used for translating string indices to line/column numbers and for tracking multi-line comment state.
 * `Whitespace`: Base psuedo-lexer, parses whitespace
 * `Lexer`: Extends `Whitespace`, parses basic tokens such as identifiers, etc.
 * `Types`: Extends `Lexer`, parses type specifiers
 * `Expressions`: Extends `Types`, parses C0 imperative expressions
 * `Specifications`: Extends `Expressions`, parses Gradual C0 expressions and annotations used in specifications
 * `Statements`: Extends `Specification`, parses C0 imperative statements
 * `Definitions`: Extends `Statements` and `Types`, parses Gradual C0 struct, type, method, and predicate definitions
 * `Parser`: Extends `Definitions`, contains helper methods for creating a parse state, parsing various contexts, and returning the parsed AST.
