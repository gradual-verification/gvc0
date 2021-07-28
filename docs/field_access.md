# Runtime Verification of Field Access

## Motivation

Partial verification requires the ability to verify the validity at run time of assumptions made to complete the proof of program behavior. Most assumptions can be verified by simple asserts of the current program state, for example, `x == 1` or `x < 10`. However, field accessibility permissions, which are used by IDF, require additional state to be mutated in order to assert the required permissions at run time. This document outlines a few methods to store, update, and verify these permissions in a partially-verified C0 frontend.

Note that fractional permissions (for example, concurrent readers of one value) will not be considered in this document.

## Fields

First, we must define what we are tracking and verifying. IDF tracks permissions of fields of objects that are on the heap. Since C0 does not allow stack-allocated structs, all structs are allocated on the heap, and thus all accesses of struct fields must be verified, either statically or dynamically. Furthermore, multiple allocations (instances) of the same struct type must have different field permission sets. For example, if `x` and `y` reference different addresses, access to `x->a` is tracked and verified independent of access to `y->a`.

Thus, field permissions must be identified by a pair of both the instance and the field. For purposes of this document, unless otherwise specified, a "field" will mean a particular field of a particular object, not a particular field of all objects of that type.

## Data Structures

A permissions store will track the current fields that a method has permission to read and write. Before discussing assertions of and updates to the permissions store, we must outline the structure of the permissions store. At its core, a permissions store is simply a set of fields. As mentioned previously, a field must be identified by both the instance allocated and the field name (or other identifier).

Thus, a permissions store must contain a collection of pairs of instance and field identifiers.

Example definition:
```c
struct FieldPermission {
  int instanceId; // or other type, see "Instance Identification"
  int fieldId;
};

struct PermissionStore {
  struct FieldPermission[] permissions;
};
```

### Field Identification

Instead of specifying the string name of a field, fields can be identified by unique integers assigned at compile time. For example, given the following definitions:

```c
struct Box {
  int height;
  int width;
}
```

At compile time, the `height` field would be assigned an identifier of `0` and the `width` field could be assigned an identifier of `1`.

Then, when tracking access to `boxValue->width`, the permissions store can uniquely identify the field by the instance (`boxValue`) and the field ID of `1`, instead of needing a string value `"height"` which requires more memory and slower comparisons.

### Instance Identification

C0 provides limited methods to identify instances. There are no casts of pointers to `int`s, and there are no `void*` pointers to an untyped memory address. The following are three other options of identifying instances of objects:

**Option 1: Rewrite allocations to add an integer identifier**

This method requires three components: a global counter, rewriting of structs, and rewriting of allocations.

First, a global counter could be added to every method by means of the permissions store. Since methods may already need access to the permissions store, we can add a field, say `permissions->instanceCounter`, which stores a pointer to a single int value. A permission store containing this counter would then need to be passed to every method performing an allocation of a `struct` value.

Second, every struct definition could be rewritten to add a special field, say `_id`, which is meant to contain an `int` value that is unique to the instantiation of the struct.

Finally, every call to `alloc` or `alloc_array` could be rewritten. After every call `alloc` or `alloc_array` of a `struct` type, for each instance allocated, code equivalent to `instance->id = *permissions->instanceCounter; (*permissions->instanceCounter)++;` would be inserted.

Pros:
 * Integer identifiers, which makes BSTs or hash tables possible
 * Implementable in C0 source code

Cons:
 * Extensive rewriting of struct types and source code
 * Counter pointer must be passed to every method that performs a struct allocation
 * Could cause integer overflows when allocating too many instances

**Option 2: Use separate stores for each struct type**

Instead of lumping all struct instances together, an alternative implementation could identify instances by their pointer and type. For example, permissions of `struct A` instances would be tracked separately from `struct B` instances. Thus, the permissions store would be split into multiple sets, where each set tracks instances of a separate struct definition. The permissions store definition would be automatically generated at runtime.

For example, given the following source code:
```c
struct A { int value; };
struct B { string name; };
```

The frontend would generate the following code to define the permissions store:

```c
struct FieldPermissionA {
  struct A* instance;
  string field; // or other identifier for the field
};

struct FieldPermissionB {
  struct B* instance;
  string field;
};

struct PermissionsStore {
  struct FieldPermissionA[] A;
  struct FieldPermissionB[] B;
};
```

Pros:
 * Less rewriting of source code
 * Implementable in C0 source code

Cons:
 * Generated code increases as more struct types are used
 * No comparison (other than [in-]equality) of pointers (I.E. `ptrA < ptrB` is prohibited) which precludes the implementation of hash tables or BSTs.

 **Option 3: Use C1 generic pointers**

While C0 does not have any pointer type that can reference multiple struct types, C1 does, in the form of `void*` pointers. Thus, instances would be identified by casting the pointer to a `void*` type.

Pros:
 * Less rewriting of source code

Cons:
 * Requires C1 output
 * No comparison (other than [in-]equality) of pointers (even in C1) which precludes the implementation of hash tables or BSTs.

## Tracking Permissions

Once the data structure of the permissions store is established, we can begin to track which fields a given method has access to.

### Option 1: Track all field permissions

This option tracks all field permissions at run time, regardless of whether this information is required. This approach should simplify the implementation since it does not distinguish between precise or imprecise contexts. It does, however, add unecessary overhead for fully-specified methods.

With this option, collecting field permissions from predicates is done inside the method. This allows method calls to call the function directly without verifying the precondition, but adds overhead since this must be done even when the precondition can be statically proven.

 * Every method is augmented with an additional argument for the caller's permission store.
 * At each method entry point, code is inserted to create a new permission store that contains a subset of the caller's permissions, collected using the precondition predicate(s).
 * At each allocation in the method, permissions are added to the method's permission store.
 * At each method call, the entire permission store is passed.
 * Before returning, the caller's permission store (passed as an argument) is augmented with permissions collected from the predicate if the postcondition is precise, or all permissions if the postcondition is imprecise.

### Option 2: Track field permissions only in imprecise contexts

This option skips tracking field permissions when it is known to be unecessary. This requires distinguishing between precise or imprecise contexts. An *imprecise context* is any code in a method with an imprecise pre- or post-condition or following an invoke of a method that has an imprecise postcondition. In either of these contexts, the method may have additional field permissions that cannot be proven statically with IDF.

With this method, collecting field permissions from predicates is done at the call site for methods with , before the method is called. This allows omitting the dynamic execution of predicates when supporting specifications are specified.

 * All methods are augmented with an additional argument that specifies the permission store of the caller.
   * At method entry, if the pre-condition is imprecise:
     * Caller permission store must not be `NULL`.
     * A copy of the permission store is created that contains a subset of the caller's permissions collected using the precondition predicate (all permissions if imprecise).
     * The entire method is considered an imprecise context, using this copy of the permission store for any runtime checks.
   * At method entry, if the pre-condition is precise:
     * Caller permission store may be `NULL`, indicating that it is called from a precise context.
     * No copy is made of the permission store. Instead, if the method switches to an imprecise context, the permissions are determined from statically-proven information.
   * Prior to method return, if the post-condition is precise:
     * If the caller permission store is not `NULL`, add all permissions collected from the post-condition predicate to the caller's permission store (post-condition predicate could query runtime permission store if return is in an imprecise context).
     * Note: simple optimization could be made to not inject this code, and even drop the permission store argument, if it is known that the method is only called from precise contexts.
   * Prior to method return, if post-condition is imprecise:
     * Caller permission store must not be `NULL`
     * All permissions, either determined statically in a precise context, or from the permission store if in an imprecise context, are copied to caller's permissions.
 * Method calls are implemented differently depending on both the context and the method's specifications:
   * Precise context, calling method with precise pre/post conditions:
     * Method calls are executed directly, passing `NULL` for the permission store.
   * Precise context, calling method with imprecise pre-condition:
     * A new permission store is created.
     * All permissions collected statically (need more info from Viper) are added to the permission store.
     * Method is called, passing it the new permission store
   * Precise context, calling method with imprecise post-condition:
     * Follow steps in previous category to call method.
     * After method is called, switch to an imprecise context, using the newly-created permission store.
   * Imprecise context:
     * Call method, passing it the current permission store

### Further Optimization Ideas

 * For methods that do not include runtime checks of permissions and do not return permissions, remove all permission-tracking code. This would need to be repeated until no more methods are identified in order to optimize method chains.
 * For methods that return the same permissions, and do not replace instances (most likely many methods would meet these requirements), eliminate mutation or copy of the permission store.

## Predicates

Predicates are used for two purposes at run time: verification of specifications and collecting permissions.

### Verification

While predicates can be modeled as a boolean-returning function for the programmer, at run time, a predicate failure will result in program termination. Therefore, we can model predicates as `void` methods since they either execute successfully, indicating that the predicate was satisfied, or result in an execution error, indicating that the predicate was not satisfied.

If a predicate must be executed for verification at runtime, each logical condition is asserted. The predicate must also be passed a permission store, containing the current permissions (predicates will only be verified at run time in imprecise contexts where a permission store already exists). When field permissions are asserted, a copy of the permission store must be created. Every field permission asserted is then removed from this copy and not allowed to be referenced by other assertions in the current predicate execution in order to preserve the semantics of separating conjunctions.

**Question**: When Viper determines that a predicate cannot be statically proven to succeed, will the required run time check reference the predicate or the condition needed for the predicate to succeed? I.E. if `predicate P(x) := x > 0` is required, will the runtime check be `P(x)` or `x > 0`?

### Collecting Permissions

In addition to verification, predicates may be used to collect permissions that are statically proven to exist but are indefinite. For example, from an imprecise context, a precisely-specified method may be called that ensures a recursive predicate in the post-condition. When calling the method, even though the recursive predicate is proven to exist (in equi-recursive terms, be valid at run time), the exact permissions must be identified and added to the current permission store since they may be queried by run-time checks in following code.

**Question**: When collecting permissions, is an input store required, or all the satisfying permissions already verified to exist? I.E. when requiring a predicate in an imprecise context, will runtime checks be inserted to verify the predicate?

An implementation of a predicate that collects permissions requires two permission stores: an input store containing the available permissions if not known statically, and an output store containing the collected permission. The input store may be `NULL` if called in a precise context where the required permissions are proven statically to exist. In addition to the permission stores, any arguments of the predicate are also passed. The predicate is executed, and anywhere an `acc(field)` is encountered, the field is removed from the input store and added to the output store. If the field does not exist in the input store, or if the field already exists in the output store, the predicate must fail since field permissions may currenly only be combined with separating conjunctions.

### Folding/Unfolding

**Question**: Can folds/unfolds be ignored at run time? The requirements for folding/unfolding should be either statically proven or the required runtime checks should be indicated by Viper.
