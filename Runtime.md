# Runtime Checks

## Accessibility

Accessibility permissions can be checked/acquired at runtime by inserting an additional field into the struct for each original field. For example, if we have a struct with `int value;`, we add an additional field `bool value_perm;` that will be `true` if the permission is currently acquired and `false` if it is not currently acquired.

### Preconditions

If a function includes an optimistically assumed precondition of `acc(a->value)`:
 1. `assert(!a->value_perm);` - Assert that `a->value` is not currently accessible to any other method.
 1. `a->value_perm = true;` - Acquire accessibility of `a->value`.

### Postconditions

If a function includes an optimistically assumed postcondition of `ensures acc(a->value)`:
 1. `assert(a->value_perm);` - Assert that `a->value` is currently accessible to this method.
 1. `a->value_perm = false;` - Release accessibility of `a->value`.

### Notes

 1. We cannot rewrite library structs to include permission fields, but library structs are required to be undefined. Therefore the individual fields of library structs cannot be accessed which removed the need for accessibility checks of these fields.

### Questions

 1. If an accessibility permission is optimistically assumed for an `ensures` or `requires`, is the corresponding accessibility permission also assumed? For example, if `requires acc(a->b);` is assumed, is `ensures acc(a->b);` also assumed so that the permission is not lost?