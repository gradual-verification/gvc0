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

1. Remove all permissions specified in the method's precondition from the `OwnedFields` instance.
2. Call the precise method, passing the object counter pointer from the `OwnedFields` instance.
3. Add all permissions specified in the method's postcondition to the `OwnedFields` instance.

Each precondition and postcondition must be executed in the case where conditionals are present. If no conditionals are present in either specification, then the net difference in permissions can be calculated statically to produce a set of operations that minimally modify permissions before and after the callsite.
### Calling imprecise methods

If an imprecise method has an imprecise precondition, pass the `OwnedFields` instance verbatim. Any mutations to the permission set are inherited by the caller.

However, if the method has a precise precondition and an imprecise postcondition, the following steps occur. 

1. Instantiate a temporary `OwnedFields` and populate it with the permissions given by the precise precondition.
2. Call the imprecise method, passing this temporary instance verbatim. 
3. Merge the temporary `OwnedFields` instance with the primary one.
## Runtime checks

Runtime checks assert the presence of a specified permission in the executing method's permission set. This will only occur in an imprecise method, or in a precise method after calling an imprecise method, so an `OwnedFields` instance will always be available. 
### Separating conjunctions
 A separating conjunction can separate permissions that are statically-known from permissions that must be dynamically-checked. To satisfy this, any statically-known permissions that are included in the larger specification must be removed before dynamically checking a permission.
### Implementation
To assert the presence of a permission:

1. Create a temporary `OwnedFields` instance.
2. Walk the specification (pre-condition, loop invariant, assert, or post-condition), asserting that each access permission is present in the primary `OwnedFields`.
3. After a permission is dynamically asserted to be present, if it is separated from other permissions, then assert that it is not already present in the temporary `OwnedFields`. Then, add it to the temporary `OwnedFields`.  

Any runtime checks that arise separately from a permission (i.e. `acc` of a field created by a field assignment statement) can be asserted without modifying the set of permissions since there are no separating conjunctions.

When translating a specification for the runtime check procedure, all accessibility predicates for structs of a different type than that of the permission(s) that must be checked can be ignored, as it is impossible for them to violate the separating conjunction.

## Abstract Predicates
Abstract predicates are translated into *predicate functions* that modify the contents of `OwnedFields` structs for  each access permission in the predicate's body.

When a predicate is used to support a runtime check, a predicate function is generated and called that takes both primary and temporary `OwnedFields` structs. It performs the runtime checking procedure for each permission in the predicate's body; asserting that a permission is present in the primary `OwnedFields` and, if necessary, asserting that it is *not* present in the temporary `OwnedFields` before adding it to this secondary struct.

Whenever a predicate is used in a precise specification, its permissions must be unrolled into or out of the primary `OwnedFields` as necessary. Two predicate functions are generated for these situations; each of which either adds or removes each permission in the predicate's body from the primary `OwnedFields` struct.

## Questions

Based on our current rules, we'll definitely need to unroll predicates that are used preconditions and postconditions of fully specificied methods, as well as for the precise precondition of an imprecise method.
Will we need to do this for *any* predicate used in *any* specification, precise or imprecise, to track the permissions that we'll gain or lose? 

Do we need to assert separation when unrolling a predicate for the purpose of capturing its permissions in the primary `OwnedFields`, or will this only be necessary for when we're performing a runtime check?