# Transformations

## Struct Flattening

### Definition

Given the following C0 code:
```c
struct Inner { int value; };
struct Outer
{
  struct Inner inner;
  int value;
};

...

struct Outer *value = ...;
print(value->inner.value);
```

Transform it to the following:
```c
struct Outer
{
  int inner_value;
  int value;
};

...

struct Outer *value = ...;
print(value->inner_value);
```

### Motivation

C0 disallows bare (non-pointer and non-array) struct values (also called large values) when used as arguments, variables, or expressions used as statements. C0 also allows declaring bare struct values inside other structs. Given both specifications, only the values in a bare struct embedded in another struct will every be accessed; the entire struct can never be accessed or copied directly.

Moreover, Silver only allows one level of member access as L-Values. For example, `a.b = 1` is valid, but `a.b.c = 1` is not valid. Thus, when targeting Silver, we need to rewrite nested member accesses (`a.b.c` -> `$ab = a.b; $ab.c`), but when targeting C0 we cannot rewrite nested members in the same way (doing so would introduce bare struct values on the stack). To avoid both problems, we can rewrite embedded bare structs, inlining all the embedded struct members directly in the parent struct. This can be done since the embedded struct can never be accessed directly in C0.

### Notes

 * This method must be used recursively to accomodate multiple levels of nested structs.
 * Rewritten fields must not shadow existing fields in the struct.
 * Pointers to structs cannot be rewritten in the same way since the pointer itself may be referenced.
 * After this pass, all dotted member accesses may be avoided. (The only possible case is `(*a).b` which can be rewritten as `a->b`.)

## Transforming to SSA

### References

 * Braun et. al: Tranlation from CFG or AST to SSA - https://pp.ipd.kit.edu/uploads/publikationen/braun13cc.pdf
 * Single-pass translation from structured AST (no GOTO) to SSA: https://www.researchgate.net/publication/220404723_Single-Pass_Generation_of_Static_Single-Assignment_Form_for_Structured_Languages
 * Simple conversion to SSA: https://link.springer.com/content/pdf/10.1007%2F3-540-46423-9_8.pdf
