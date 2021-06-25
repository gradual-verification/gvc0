# Checks for validation

 * Check that every assignment left-hand side is an L-Value
 * Ensure that every non-void method terminates in either a return or error
 * Ensure that reserved words are not used for any identifier
 * Ensure that `#use` directives precede all other definitions
 * Ensure that `\result` and `\length` are only used inside annotations
 * Ensure that `requires` and `ensures` are only used in method annotations
 * Ensure that `loop_invariant` is only used in `while`/`for` annotations
 * Ensure that `assert` annotations are only used in statements
