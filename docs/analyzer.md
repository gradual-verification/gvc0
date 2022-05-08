# Analyzer

The analyzer implements a resolver, type-checker, and basic program analyzer. It checks parsed source code for errors.

Most interaction with the analyzer should be through the interfaces defined in the `Validator` object, but specific methods in the `Resolver` object or specific `*Validator` objects may also be used as required.

## AST Definitions

The analyzer uses an AST format that is separate from the parse AST. While the parse AST uses string values for variable IDs, method names, etc., the resolver maps these string values to the declarations that are referenced. This allows the type-checking and program analysis to efficiently check that the references are being used correctly.

The resolved AST is defined as immutable `case class`es, since mutation is generally not required during analysis.

Each resolved AST node contains a reference to the parsed AST node from which it was created. This allows error messages to reference the location in the source code where the error occurred.

The resolved AST also contains error nodes so that multiple errors may be caught in a single resolving pass, and so that a partially resolved AST may be returned even in the presence of errors. If no errors are emitted during resolving, it may be assumed that no error nodes are contained in the resolved program.

The analyzer AST is defined in the following files:

* `Expressions`: expressions (both imperative and specification)
* `Headers`: `#use` declarations
* `Methods`: method declarations
* `Statements`: imperative statements
* `Structs`: struct definitions
* `Types`: type references and declarations
* `Variables`: variable definitions

## `Errors`

Errors are collected in a `ErrorSink` object. Each stage of the analyzer may add errors to the error sink. The analyzer is designed so that all analysis passes may be run on any parse tree, even if the parse tree contains invalid definitions or expressions. This allows errors from multiple analyses to be returned immediately to the user. However, type-checking should complete without errors before running analysis passes.

A parse AST `Node` is attached to each `Error` object, which specifies the location in the source code from which the error originated. This AST node may be referenced for information such as line/column numbers.

## `Resolver`

The resolver converts the [parser AST](parser.md) to the resolved AST used throughout the analyzer. Its main function is to resolve identifiers, such as method or variable names, to the corresponding declaration. Variable scope rules are implemented.

Any invalid references, such as references to undeclared variables or methods, are partially resolved. In these cases, an error is always emitted, and a special resolved node may be used to indicate an error (for example, `MissingNamedType`).

## `TypeChecker`

Validates the types of expressions, predicate parameters, method parameters, and method return values are used correctly (i.e. that uses match the declared types). Unresolved types are ignored, since errors for these are emitted in the resolver.

Type checking C0 is straightforward since C0 does not implement sub-types. However, care must be taken for the `NULL` values, since these values may be used for any pointer type. Therefore, the resolved AST includes a special `NullType` that is in some ways regarded as a sub-type of all pointer types.

The type checker also enforces that "large" values (i.e. non-atomic values such as entire structs) are not stored on the stack, in accordance with C0 requirements. It also enforces that `acc()` expressions are only used for fields or pointers, not bare variables.

## Analysis Passes

After resolving and type-checking complete successfully, the analysis passes are run. These are basic program analysis passes that implement the same error checking as `cc0`. These are separated into several distinct passes, but all passes may be run without regard to the success/failure of other passes.

 * `AssignmentValidator`: Checks for use-before-assign errors
 * `ImplementationValidator`: Checks that all non-library methods are actually implemented (not just declared).
 * `ReturnValidator`: Checks that all non-void methods return a value on all possible code paths. Also, (NON-STANDARD!) checks that all return statements are in the tail position (disallows early returns). Note: this is only required because Gradual Viper does not yet implement the necessary control flow statements to implement early return.
 * `SpecificationValidator`: Checks that specifications are well-formed (`acc()` expressions and predicates are only allowed in top-level conjunctions, imperative methods/allocations are not allowed in specifications, etc.)
