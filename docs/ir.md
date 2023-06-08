# Transformer/IR

The GVC0 IR is a low-level representation for instructions that can target both C0 and Silver. Since it directly targets Silver, its expressivity is limited compared to the normal C0 AST used in the parser or analyzer. The transformer lowers the analyzer AST into IR by emitting (possibly multiple) IR ops for each expression or statement in the C0 AST.

## IR API

The IR is a relatively simple AST structure that is mostly mutable. The data structures are defined in `src/main/scala/gvteal/transformer/IR.scala`. Due to its mutability, care must be taken to preserve validity in the AST structure. Some checking of validity happens statically through the type system, or at runtime with exceptions. However, there are many possibilities for generating invalid code in the IR.

**Note:** referential equality (not structural equality) is used throughout. For example, two separate `Var` instances are considered distinct, even if they share the same name. This is to eliminate mishandling of vars, fields, etc from separate programs or methods. As a consequence, the exact instance returned from `addMethod`, `addVar`, etc. must be always used when referencing that method or var. **Do not** instantiate IR objects directly, except the root `Program` instance, expressions, and ops.

### Program

Each program contains a collection of structs, methods, predicates, and dependencies. Header definitions are not represented in the program; instead, it only contains implementations of methods, structs, and predicates. Definitions without an implementation are allowed only in dependencies.

Programs are initially created empty. Child nodes are created via the `addStruct`, `addMethod`, etc. methods.

### Struct

Use the `Program#addStruct` method to define a struct. The newly-created struct that is returned will be empty. Fields are added using `Struct#addField`. As mentioned above, the field instances returned by `Struct#field` or `Struct#addField` must be used; do not instantiate `StructField` objects directly.

The struct name is immutable, but its fields are mutable.

Struct fields avoid name collisions by appending a number to the name passed to the `addField` method. Note that this does mean that the name of the added field may not match the name passed to `addField`. Instead, the name of the returned `StructField` must be used instead.

### Method

Use the `Program#addMethod` method to define a method. The newly-created method will have no parameters or ops. Parameters are added using `Method#addParameter` to add parameters. Use the `Method#body` field to access the root block and add ops to the method.

Variables can only be defined at the top-level of the method; block-scoping does not exist in the IR. Define variables in the method with the `addVar` method.

Parameters and variables avoid name collisions; the name of the variable may not match the name passed to `addVar`. Instead, use the name of the returned `Var`.

### Predicate

Use the `Program#addPredicate` method to define a predicate. The newly-created predicate that is returned will be empty. Like methods, add parameters using the `Predicate#addParameter` method. Predicates only contain a root expression which may be accessed via the `Predicate#expression` field.

Note that predicate names do not use name collision avoidance; an error will be thrown if multiple predicates with the same name are defined in the same program.

### Block

Blocks are doubly-linked lists of ops, and are used in methods and ops such as `if` that contain other ops. Blocks are mutable; ops may be appended or prepended using the standard `+=` or `:+=` methods, respectively. Similarly, multiple ops may be added using `++=` or `:++=`.

### Op

An `Op` represents a single statement in a method. Ops must be directly instantiated and added to a block. When added to a block, ops act as nodes in a doubly-linked list. Use `Op#insertAfter`, `Op#insertBefore`, `Op#remove`, and other methods to manipulate the linked list of ops in the block.

**Note:** Ops may only belong to a single block at a time. Attempting to add an op to multiple blocks will result in an exception.

Ops are a subset of C0 statements. Some C0 statements require rewriting to simpler ops, which is handled by the transformer.

### Expression

An `Expression` represents a subset of C0 expressions. However, IR expressions cannot contain side-effects. Any side-effects (such as method calls) are handled in ops, and the transformer implements this conversion. In addition, IR expressions do not distinguish between expressions that may be used only in specifications and expressions that may only be used in ops. Care must be taken to ensure that all expressions are used only in contexts where they are valid.

Expressions may be directly instantiated, except for scoped expressions such as vars which must be defined in their parent scope.

**Note:** Expressions are **immutable**, and re-using an expression instance in multiple ops or multiple expressions is supported. (And necessary for `Var` expressions, for example, given the referential equality previously discussed.)

## Transformer

The transformer converts the analyzer AST into the IR. It is mostly contained in `src/main/scala/gvteal/transformer/IRTransformer.scala.

While much of the translation process is straightforward, it may involve converting some expressions or statements into multiple IR ops. This is necessary since C0 expressions may contain side-effects (namely method calls and allocations), which must be converted to separate ops in the IR. As each expression is converted, a scope object (see below) is passed along that tracks the current position to insert any ops. When a side-effectful expression is encountered, a new variable is created to store the result, and an op which implements the side-effect is added to the current scope. The temporary variable is then used in place of the original expression.

### Scopes

Any generated ops must be inserted in the correct position and preserve short-circuiting behavior. To do this, the transformer uses scopes that track the current position in the output IR and any necessary state. Every scope carries a mapping of variable names to the IR variables, since IR variables may use differing names from their source name due to collision avoidance (see the Method section).

There are several implementations of the transformer `Scope` trait, each used for a specific purpose. The most basic is `BlockScope`, which simply appends any ops that it receives to a block.

A `ConditionalScope` appends ops to a block, but first wraps them inside an `if` block. This is for converting side-effect-containing expressions in a branch of a ternary statement (i.e. `x ? y() : z()`).

A `CollectorScope` simply collects ops into a list, which is then processed separately. This is for converting side-effect-containing expressions in a loop condition, which must be evaluated prior to the loop and after every iteration. This is handled by collecting all ops into a list, and then duplicating them for both the loop start and the tail of the loop body.

A `PredicateScope` does not allow inserting ops, since it is used for a predicate body. It also only contains a mapping of parameters, not variables, since variables may not be used in predicate bodies.

### Struct Flattening

The transformer also rewrites struct to embed the fields of any struct values directly in the parent struct.

For example:

```
// Input:
struct Point {
  int x;
  int y;
};
struct Line {
  struct Point start;
  struct Point end;
};

Output:
struct Line {
  int start_x;
  int start_y;
  int end_x;
  int end_y;
};
```

This rewriting step allows all field accesses in the IR to be pointer dereference, i.e. arrow field accesses such as `x->y`. This is necessary since Silver does not implement value semantics as used in dot field accesses such as `x.y`. Since C0 does not allow storing field values directly on the stack, the only instances of dotted field accesses occur when accessing nested fields such as `line->start.x` in the example. Thus, this rewriting pass eliminates all instances of dotted field accesses. This rewriting is handled in the `resolveField` method in the transformer, as well as supporting data structures and methods.
