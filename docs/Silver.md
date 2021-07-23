# Silver API

An overview of the Silver API, primarily its AST data structures.

## Parse AST

Used by the parser. Not used by existing frontends (at least in Gobra).

 * `PNode`: Base class for all parse AST nodes
   * Contains methods for traversing the AST
 * `TypeHelper`: Contains primitive types
   * `Int`, `Bool`, `Perm`, `Ref`, Predicate, Wand
 * `PIdentifier`: Trait, references a name
   * `PIdnDef`: Definition of an identifier, basic node
   * `PIdnUse`: Usage of an identifier, expression
 * `PFormalArgDecl`: Declaration of formal argument, typed node
 * `PDomainTypeKinds`: Unresolved, Domain, TypeVar, or Undeclared
 * `PType`: Reference a type
   * `PPrimitiv`: objects of this type are instatiated in `TypeHelper` for primitive types such as `Int`
   * `PGenericType`: contains a list of type arguments
     * `PDomainType`: takes a list of type arguments
     * `PGenericCollectionType`
       * `PSeqType`
       * `PSetType`
       * `PMultisetType`
   * `PInternalType`
     * `PUnknown`
     * `PPredicateType`
     * `PWandType`
 * `PExp`: Represents an expression
   * **`PImpreciseExpr`**: Wraps another expression and adds imprecision
   * `PMagicWandExp`
   * `POpApp`: an operator application (trait)
     * `PBinExp`: a binary operator usage (left, right, operator name)
       * Valid operators: `+` `-` `*` `/` `\` `%` `<` `<=` `>` `>=` `==` `!=` `&&` `||` `<==>` `==>` `--*` `in` `++` `union` `intersection` `setminus` `subset`
     * `PUnExp`: an unary operator usage (operator and expression)
       * Valid operators: `-` `!`
     * `PCondExp`: a conditional expression, i.e. a ternary (condition, value if true, value if false)
     * `PHeapOpApp`
       * `PResourceAccess`
         * `PLocationAccess`: refs an identifier
           * `PFieldAccess`: (receiver, field identifier)
           * `PPredicateAccess`: (arguments, predicate identifier)
           * `PUnfolding`: (accessibility predicate, expression)
       * `PInhaleExhaleExp`: (formal arg declaration, body expression)
       * `PCurPerm` (resource access)
       * `POldExp`
         * `POld` (expression)
         * `PLabelledOld` (label, expression)
     * `PApplying`: (wand expression, expression)
   * `PCall`: a function call (contains a `PIdnUse` and a list of `PExp` for args)
   * `PSimpleLiteral`: any literal
     * `PIntLit`
     * `PResultLit`: ?
     * `PBoolLit`
     * `PNullLit`
     * `PNoPerm`
     * `PFullPerm`
     * `PWildcard`
     * `PEpsilon`
     * `PAccPred` (location access, permission expression)

   * `PBinder`
     * `PQuantifier`
       * `PExists`
       * `PForall`
       * `PForPerm`
     * `PLet`: represents a `let` expression
     * PLetNestedScope`: artifact of `PLet`, used to implement proper resolver semantics
     
 * `PTrigger`: contains a list of expresions
 * `PTypeSubstitution`: Contains a map of strings to types. Unknown usage?
   * `PTypeRenaming`
 * (Omitting a bunch of Seq-related stuff)
 * `PStmt`: represents a statement
   * `PSeqn`: sequence of statements
   * `PFold` (expression)
   * `PUnfold` (expression)
   * `PPackageWand` (wand expression, proof sequence)
   * `PApplyWand` (expression)
   * `PExhale` (expression)
   * `PAssert` (expression)
   * `PAssume` (expression)
   * `PInhale` (expression)
   * `PVarAssign` (identifier ref, expression)
   * `PFieldAssign` (`PFieldAccess`, expression)
   * `PMacroAssign` (call, expression)
   * `PIf` (condition expression, if sequence, else sequence)
   * `PWhile` (condition expression, invariant expression, body sequence)
   * `PLocalVarDecl` (identifier, type, optional expression)
   * `PGlobalVarDecl` (identifier, type)
   * `PMethodCall` (identifier refs for targets [vars which will be assignd the return values], method name identifier, argument expressions)
   * `PLabel` (identifier, invariant expressions)
   * `PGoto` (identifier)
   * `PTypeVarDecl` (identifier)
   * `PMacroRef` (identifier ref)
   * `PDefine` (identifier, optional parameters, body node)
   * `PSkip` (empty)
   * `PNewStatement` (target identifier ref)
     * `PRegularNewStmt` (target, list of fields)
     * `PStarredNewStmt` (target)
 * `PScope`: assigns a unique scope ID number
 * `PProgram` (imports, macros, domains, fields, functions, predicates, methods, extensions, errors)
 * `PImport`
   * `PLocalImport`
   * `PStandardImport`
 * `PMethod` (identifier, formal args, formal return args, preconditions, postconditions, optional body statement)
 * `PDomain`
 * `PFunction` (identifier, formal args, type, preconditions, postconditions, optional body statement)
 * (Omitting a bunch of domain-related stuff)

## Resolver

 Runs `NameAnalyser` and `TypeChecker` on the parse AST.

## `TypeChecker`

Performs type-checking and sets the types of all typed nodes. Operates on the parse AST. Macro definitions should have been removed.

 * Finds named macros
 * Checks that all folded and unfolded predicates are defined (not abstract)
 * Checks for valid L-Values
 * Checks that only fields are passed to `new()` expressions
 * Verifies number of arguments for method calls and return parameters
 * Label invariants must be boolean typed
 * Checks fields (possibly including a class?)
 * If conditions must be boolean
 * Invariants must be boolean

## `NameAnalyser`

Resolves identifiers to their declaration. Operates on the parse AST.

 * Contains global, local, and universal maps
 * Universal map seems to not be used?
 * Contains set that specifies the names currently in scope
 * Local identifiers cannot shadow global identifiers

## `Translator`

Converts the parse AST to the Silver AST.

 * Different representation for permission operations vs. arithmetic operations
 * Nodes with no position are changed to `SourcePosition(null, 0, 0)`

 ## AST

 * `Node`: Base class for all AST nodes
   * `.check` method to check for consistency
 * `Info`: Additional information for nodes such as comments
   * `NoInfo`
   * `SimpleInfo` (comments)
   * `AutoTriggered`: related to quantifiers
   * `Cached`: mark pre-verified node
   * `Synthesized`: mark node created from a transformation
   * `ConsInfo`: combines multiple infos
 * `Infoed`: node with info
 * `Positioned`: node with position
 * `Typed`: node with type
 * `Declaration`: declaration of something
 * `Scope`: node that defines a new scope

## AST Positions

 * `Position`: base for all position objects
 * `NoPosition`: position is not available
 * `HasLineColumn`: base for position with a line and column
 * `HasIdentifier`: base for position that references an identifier, identifies the origin of a node
 * `LineColumnPosition`: concrete class for line/column positions
 * `AbstractSourcePosition`: base for source positions (file, start, optional end)
 * `SourcePosition`: concrete class for source positions (file, start, optional end)
 * `IdentifierPosition`: concrete class for source positions with an identifier
 * `TranslatedPosition`: concrete class that wraps an `AbstractSourcePosition` and refers to a position in a source language that has been translated to Viper

 ## Program AST

  * `Program` (domains, fields, functions, predicates, methods, extensions)
    * Type-checks method calls (`checkMethodCallsAreValid`)
    * Checks unfolding/fold of abstract predicates (`checkAbstractPredicatesUsage`)
    * Type-checks function calls (`checkFunctionApplicationsAreValid`)
    * Type-checks domain functions
    * Verifies identifier usages (variables, methods, functions, fields, predicates, gotos, labeled old)
 * `Field`: Field declaration (name, type)
   * Verifies that type is concrete
 * `Predicate`: Predicate declaration (name, args, optional expression)
   * Must not contain old expressions
   * Must not contain perm/forperm expressions
 * `Method`: Method declaration (name, args, returns, preconditions, postconditions, optional body sequence)
   * Scope includes both arguments and return values
   * Return values cannot be used in preconditions
   * Can be converted to CFG
 * `Function`: A function declaration (name, args, return type, preconditions, postconditions, optional body)
 * `LocalVarDecl`: local variable declaration; not a statement (name, type)
 * (Omitting a bunch of domain-related stuff)
 * Operators
   * `AddOp`, `SubOp`, `MulOp`, `DivOp`, `ModOp`
   * `NegOp`
   * `LtOp`, `LeOp`, GtOp`, `GeOp`
   * `OrOp`, `AndOp`, `ImpliesOp`
   * `NotOp`