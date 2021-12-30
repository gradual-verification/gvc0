# Runtime Checks for Field Access Predicates

## Tracking Allocations

If a function has a complete, statically-verified specification, and it does not call any partially specified functions, then no runtime checks are required in its immediate body. However, because it may allocate memory, an `_id_counter` variable is injected as a parameter to assign unique IDs to each struct allocation. This is initialized once at the entry of the program, and is incremented for each allocation. Each struct's definition is injected with an `_id` field to contain its unique identifier. 

If a precise function calls imprecise functions, or if a function itself is imprecise, then `OwnedFields` structs must be introduced to track which fields become accessible and inaccessible during runtime. 

We differentiate between field permissions that are explicitly specified and those created at runtime by allocations. The struct `static_fields` contains static fields, while `dyn_fields` contains permissions created by calls to `alloc`. Additionally, `dyn_fields` will contain permissions that were statically verified for a different function, passed to the current one, and weren't part of any static specification in the current function.

 Note that each `OwnedFields` struct is initialized with a reference to `_id_counter` to reduce the number of injected parameters. When a struct is allocated in an imprecise context, all of its fields are marked as accessible within `dyn_fields`, and it is assigned a unique ID. 

We maintain the invariant that `static_fields` and `dyn_fields` are disjoint to handle the separating conjunction. We can verify that a field is accessible and disjoint from the statically-verified fields of a given specification by ensuring that it is only an element of `dyn_fields` and not of `static_fields`.

## Handling Imprecision

If a `?` appears in any context within a function, then `OwnedFields` structs must be created and adjusted for the function's precondition, its postcondition, and any other imprecise contracts within its body. 

### Precise Precondition

When a function with a precise precondition is called, all static permissions given by the precondition of the function are removed from the current `OwnedFields` structs. Then, the current `static_fields` and `dyn_fields` structs are stored in temporary variables and replaced by new ones. The new `static_fields` contains only the statically-verified component given by the new function's precondition, and the new `dyn_fields` is empty.

After the function returns, the current `static_fields` and `dyn_fields` are merged with their older versions, and then all permissions that are shared between the two structs are removed from `dyn_fields` to preserve separation.

### Imprecise Precondition

Similarly, all static permissions given by the precondition of the function are removed from the current `OwnedFields` structs. However, the remaining contents of `static_fields` are also added to `dyn_fields`. Then, `static_fields` is replaced with a new `OwnedFields` instance containing the static component of the new function's precondition. No temporary variables are created. 

When the function returns, permissions are similarly separated so that `static_fields` contains only the static component of the returning function's postcondition, and `dyn_fields` contains all other permissions. However, if the postcondition is precise, then `dyn_fields` is emptied.

### Assertions

To handle assertions, all permissions in the static component of the assertion are appended to the existing `static_fields` object, and separation is preserved by removing shared permissions from `dyn_fields`. Both steps occur prior to the runtime check.

## Runtime Checks

There are two types of runtime checks that can occur. A disjoint check verifies accessibility and separation, ensuring that a field is present in `dyn_fields` but not in `static_fields`. This happens for assertions that have both a precise and imprecise component. When a specification only contains `?`, separation isn't guaranteed, so we can skip the additional check against `static_fields`.