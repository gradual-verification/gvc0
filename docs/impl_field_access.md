# Field Access Tracking

## Field Identification

An `_id` field is added to each struct to uniquely identify each allocated object. (Note: the field may be named something other than `_id` if a field with that name exists already in the struct.) A `int` pointer will track the number of objects allocated. On each allocation, the new value's `_id` field is assigned the value of this counter, and the counter is incremented.

Fields are identified by the index of the field within the struct. The pair of struct `_id` and field index uniquely identify a single field in memory.

## Precise methods

A *precise method* is any method that does not contain imprecision in its pre-condition or post-condition. When calling a precise method, only the object counter pointer is passed. An additional argument is added to the method for this purpose, and every call site is updated to pass this pointer.

### Calling precise methods

When calling precise methods, pass the object counter pointer verbatim. No permissions need to be tracked since they have been statically verified.

### Calling imprecise methods

1. Initialize a new `OwnedFields` instance.
2. Add all statically-known permissions to the instance.
3. Call the imprecise method, passing it the new `OwnedFields` instance.
4. Track all following permissions and allocations in following method calls with this `OwnedFields` instance.

## Imprecise methods

An *imprecise method* is any method that contains imprecision in its pre-condition or post-condition. When calling an imprecise method, an `OwnedFields` instance must be passed. An additional argument is added to the method for this purpose, and every call site is updated to pass this pointer. The `OwnedFields` instance also contains the object counter pointer.

### Calling precise methods

1. Call the precise method, passing the object counter pointer from the `OwnedFields` instance.
2. Calculate the difference in permissions, gained or lost, from the callee's pre and post-conditions and modify the current `OwnedFields` instance accordingly (this may include predicates).

### Calling imprecise methods

When calling imprecise methods, pass the `OwnedFields` instance verbatim. Any mutations to the permission set are inherited by the caller.

## Runtime checks

Runtime checks assert the presence of a specified permission in the executing method's permission set. This will only occur in an imprecise method, or in a precise method after calling an imprecise method, so an `OwnedFields` instance will always be available. 

### Separating conjunctions
 A separating conjunction can separate permissions that are statically-known from permissions that must be dynamically-checked. To satisfy this, any statically-known permissions that are included in the larger specification must be removed before dynamically checking a permission.

### Implementation
To assert the presence of a permission:
1. Walk the specification (pre-condition, loop invariant, assert, or post-condition), and add each access specifier to a separate `OwnedFields` struct.
2. Execute the required assertion(s), checking that none of the permissions involved are contained in the temporary `OwnedFields`.
3. If the temporary `OwnedFields` struct will be reused for future runtime checks, reinitialize it as necessary.

Any runtime checks that arise separate from a permission (i.e. `acc` of a field created by a field assignment statement) can be asserted without modifying the set of permissions, since there are no separating conjunctions.

## Abstract Predicates
If an abstract predicate is present in the static component of a specification, then it is translated into a C0 function in which every access specifier is replaced with an instruction to remove the given permission from `OwnedFields` (or add it to the secondary, temporary OwnedFields struct). This function is executed during step 1 of the implementation, prior to when the runtime check occurs.