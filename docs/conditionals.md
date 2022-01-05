# Draft: Conditionals

Some runtime checks are only required for a specific execution path. In addition, Silicon's symbolic execution engine traverses every possible combination of branching, and the runtime checks required for each specific execution path are collected seperately. Thus, each runtime check usually has a list of conditions that match this specific execution path.

## Challenges

 * Runtime checks and their conditions are collected in the Viper source code, but their implementation must be in the C0 IR, and they must be mapped to the correct location in the C0 IR
 * The conditions must be evaluated at the point of branching, since code after the branch point can modify the values that introduced the branching.
 * When multiple conditions exist for one runtime check, each condition must not be evaluated unless the prior condition is satisfied. (For example, given two conditions `x != NULL` and `x->y != NULL`, `x != NULL` must be true in order to evaluate `x->y != NULL`.)
 * The number of possible execution paths (and thus combinations of branching conditions) increases exponentially. Thus, it is important to combine conditions where possible in order to produce output code of reasonable size.

## Algorithm

First, the IR operations and Viper statements are combined into one list, where each IR operation may have a corresponding Viper statement (not all IR operations produce a Viper statement). This list is then saved, because modifying the list of IR operations will destroy the sequential relation of IR operations and Viper statements.

Then, the algorithm executes two passes over this list.

## First Pass

The first pass injects runtime checks and creates variables for each condition but does not assign these new variables.

Conditional information from this pass is collected into a two-level map. This *conditional map* is keyed first by a Viper node that represents the location in code where condition(s) must be evaluated. The second level is keyed by a Viper expression that represents the value of this condition. The values contain the newly-defined IR variable that will store the result of this condition, and a list of IR expressions that represent all conditions under which the condition value may be evaluated (i.e. if any one of the conditions in this list is true, the condition may be evaluated).

```
conditional_map :=
  (vpr.Node location) ->
    (vpr.Exp value) ->
      (IR.Var variable, IR.Expression[] when)
```

Iterate over each IR operation and Viper statement pair. Lookup the list of runtime checks for the Viper statement. For each runtime check:
1. Create the `assert` statement for the runtime check.
2. Create the condition for the runtime check by iterating backwards over each branch condition (since most recent conditions are at the head of the list and depend on older conditions). Start with the IR expression `condition := true`. Then, for each branch condition:
    1. Let `location` be the node in the Viper code where the condition must be evaluated. 
    2. Let `value` be the value as a Viper expression that represents the current branch condition, not including previous branch conditions.
    3. Unwrap `value`: If `value` is of the form `!v`, let `value := v` and let `flag := false`. Otherwise, let `flag := true`.
    4. Let `value_map := conditional_map[location]`. (I.e. lookup the map at this location in the conditional map.) If there is no map at this   location, create and add an empty map.
    5. Let `(variable, when) := value_map[value]`. (I.e. lookup the second level of the conditional map, corresponding to this location and value.) If   no value exists, create and add a new value where `variable` is a new IR variable of type `bool` and `when` is an empty list.
    6. Append the current value of `condition` to the `when` list.
    7. If `flag == true`, let `condition := condition && variable`, otherwise let `condition := condition && !variable`.
3. Create the full `if` statement that executes the `assert` if `condition` is true: `if (condition) assert(...);`
4. Insert this `if` statement prior to the current IR operation.

Thus, at the end of this pass, `conditional_map` will all the condition variables that must be assigned and the conditions under which they can be evaluated, keyed by their location and value in the Viper source. Also, all runtime checks have been inserted.

## Second Pass

The remaining step adds assignments to the newly added conditional variables. Note that these assignments must be inserted at the branch point, not at the runtime check location.

Iterate over each IR operation and Viper statement pair. Let `location` be the current Viper statement. Find the second level of the conditional map for this location: ``. Then, for each key-value pair `(value -> (variable, when))` in `conditional_map[location]` (skip if `conditional_map[location]` does not exist):
1. Convert `value` from Viper into to its equivalent C0 IR expression.
2. Reduce the list of expressions in `when` by combining each expression with a disjunction. I.e. `when := (a, b, ..., n)` is converted to `when := a || b || ... || n`.
3. Create an assignment to `variable` by conjuncting `when` and `value`. I.e. `variable = when && value;`. This is so that `value` is only be evaluated when it is valid to evaluate it (i.e. when `when` is true).
4. Add this assignment before the current IR operation.

Thus, condition variables are always assigned at the specified location, but are false if they will not be needed (i.e. if it is invalid to evaluate the actual condition).

The general form of these conditional assignments is `condition = ((when_1_a && when_1_b && ...) || (!when_2_a && when_2_b && ...) || ...) && value;`

# TODO

First, inserting assignments to the conditional variable *before* the specified location may not be correct. For example, branching introduced in post-conditions must be evaluated *after* the corresponding method call. We can implement this by keying the `conditional_map` (the first level) by a combination of location and type of insertion (before/after), instead of only by location.

Also, the `when` conditions could be simplified further since these will often contain similar, but slightly different, combinations of conditions. Simplification on these terms should be straightforward since they are naturally in disjunctive normal form, and each term is a simple boolean variable which can always be evaluated without regard to execution order.
