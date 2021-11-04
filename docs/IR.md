# C0 IR

## Overview

The IR consists mainly of operations, expressions, and values.

 * Expression: an expression that returns a value. Arguments passed to expressions must be values; expressions cannot be nested. Expressions can only be assigned to a variable or evaluated in a noop operation.
 * Value: a single value that does not cause side-effects when evaluated. Must be either a variable or literal. All values may be used as an expression.
 * Operation: represents a single instruction, although it can contain multiple operations if it is a control-flow operation.
 * Block: represents a sequence of operations
 * Field: represents a field of a struct

## Operations

### `AssignVar(variable, expression)`

Assign the result of an expression to a local variable.

C0: `variable = expression;`
Silver: `variable := expression`

### `AssignMember(variable, field, value)`

Assign the given value to a field of the variable. The variable must be a pointer to a struct.

C0: `variable->field = value;`
Silver: `variable.$struct_<STRUCT_NAME>_<FIELD_NAME> := value`

### `AssignArray(variable, value, value)`

Assign the given value to the given index in an array. The variable must be an array of primitive values.

C0: `variable[index] = value;`
Silver: (undefined)

### `AssignArrayMember(variable, value, field, value)`

Assign the given value to a specific field of the value at the given index in an array. The variable must be an array of struct values (not an array of pointers).

This operation is encoded separate from a normal member assign since it accesses a struct value, not a struct reference.

C0: `variable[index].field = value;`
Silver: (undefined)

### `AssignPtr(variable, value)`

Assign the given value to the memory address specified by the pointer variable.

C0: `*variable = value;`
Silver: `variable.$ptrValue = value;` (the field `$ptrValue` changes depending on the pointer type)

### `While(value, block)`

Executes the given block while the condition value is true.

C0: `while(value) { block... }`
Silver: `while(value) { block... }`

### `If(value, block, block)`

Executes the first block if the condition value is true, otherwise executes the second block.

C0: `if (value) { block... } else { block... }`
Silver: `if (value) { block... } else { block... }`

### `Assert(value)`

Asserts that the given value is true at runtime. If it is not true, the program aborts.

C0: `assert(value);`
Silver: (skipped)

### `Error(value)`

Aborts the program at runtime.

TODO: Define Viper semantics (possibly `assert false` or noop?)

C0: `error(value);`
Silver: (undefined)

### `Return([value])`

Returns the specified value as the result of the method.

TODO: This instruction currently does not modify control flow, but it should exit the function. This can be implemented once `goto` is implemented in Viper.

C0 if `value` is specified: `return value;`
C0 if `value` is not specified: `return;`
Silver if `value` is specified: `$return = value;`
Silver if `value` is not specified: (skipped)

### `Noop(expression)`

Evaluates the given expression, including any side-effects. The only expression that can include side-effects is an `Invoke` expression, otherwise this operation can be skipped.

C0: `expression;`
Silver if expression is `Invoke`: `method(...)`
Silver if expression is not `Invoke`: (skipped)

## SpecExprifications

SpecExprifications are only used by Viper, so they only need Silver representations, not C0.

* Variable (variable)
* Field access ([variable | field].field)
* Conjunction (specification && specification)
* Relation (specification OP specification)
* Conditional (if specification then specification else specation)
* Implication (specification ==> specification)
* Accessbility (acc(specification))
* Predicate (predicate(specification...))