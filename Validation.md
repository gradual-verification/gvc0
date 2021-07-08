# Checks for validation

[X] Check that every assignment left-hand side is an L-Value
[X] Ensure that every non-void method terminates in either a return or error
[ ] Ensure that reserved words are not used for any identifier
[X] Ensure that arguments used in a postcondition are not assigned
[X] Ensure that `\result` and `\length` are only used inside annotations
[X] Ensure variables are assigned before they are used
[ ] RESOLVER: Ensure that `#use` directives precede all other definitions
[X] RESOLVER: Ensure that `requires` and `ensures` are only used in method annotations
[X] RESOLVER: Ensure that `loop_invariant` is only used in `while`/`for` annotations
[X] RESOLVER: Ensure that `assert` annotations are only used in statements

# Static Semantics Reference

[ ] `#use` directives must precede all other declarations.
[X] `TypeChecker`: All operators and functions are used with the correct number of arguments of the correct type, as explained in the sections on the various language constructs.
[X] `TypeChecker`: Operators <, <=, >=, and > are overloaded in that they apply to type int and char. Both sides must have the same type.
[X] `TypeChecker`: Operators == and != are overloaded in that they apply to types int, bool, char, t [], and t *. They do not apply to arguments of type string and struct s. Both sides must have the same type.
[X] `TypeChecker`: Structs cannot be passed to or from functions or assigned to variables.
[X] `ReturnValidator`: All control-flow paths in the body of each function end with a return statement of the correct type, unless the function has result type void.
[X] `Resolver`: Every variable must be declared with its type.
[X] `AssignmentValidator`: Along each control-flow path in the body of each block in each function, each locally declared variable is initialized before its use.
[X] `Resolver`: Function parameters and locally declared variables with overlapping scopes may not have the same name.
[X] `Resolver`: Names of functions or variables may not collide with the names of defined types.
[X] `TypeChecker`: Functions may be declared multiple times with consistent types.
[ ] Functions that are referenced (and not library functions) must be defined exactly once.
[X] `Resolver`: Structs may be declared multiple times, but may be defined at most once. Structs declared in libraries cannot be defined.
[X] `Resolver`: Type names may be defined only once (they cannot be declared).
[ ] A function int main(); is implicitly declared and also implicitly referenced, because this is the function called when an executable resulting from compilation is invoked. Therefore, when a collection of sources is compiled, at least one of them must define main to match the above prototype.
[X] `Resolver`: Field names within each struct must be pairwise distinct.
[X] `TypeChecker`: Expressions *NULL are disallowed.
[X] `TypeChecker`: Type void is used only as the return type of functions.
[X] `TypeChecker`: Expressions, used as statements, must have a small type or void.
[X] `Resolver`: Undefined structs cannot be allocated.
[X] (Only used in C1) continue and break statements can only be used inside loops.
[X] `Resolver`: The step statement in a for loop may not be a declaration.
[ ] Integer constants are in the range from 0 to 2^31.
[ ] `* <lv> ++` and `* <lv> --` must be be explicitly parenthesized to override the right-to-left associative interpretation of ++ and --.
[X] `Resolver`: `\result` is only legal in `@ensures` clauses.
[X] `Resolver`: `@requires` and `@ensures` can only annotate functions.
[X] `Resolver`: `@loop_invariant` can only precede loop bodies.
[X] `Resolver`: `@assert` can not annotate functions
[X] `Resolver`: Expressions occurring in function annotations can only refer to the functions parameters. Expressions in loop invariants and assertions can also use other local variables in whose scope they occur.
[X] `AssignmentValidator`: Variables in `@ensures` clauses cannot be assigned to in the body of the function they annotate.
