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
