## Tracking Allocations

At the beginning of `main`, a counter is allocated to provide unique IDs for each struct allocation.

```
int main () {
    int * _id_counter = alloc(int);
    *(_id_counter) = 0;
}
```

Each struct is injected with a field to contain an ID :

```
struct Node {
    int val;
    struct Node * next;
    int _id;
};
```

If a fully verified functionallocates memory, but doesn't call a partially verified function at any point, it will be given `_id_counter` as a parameter and new structs will be assigned an ID directly.
```
Node * node = alloc(Node);
node->_id = *(_id_counter)++;
```
It is necessary to pass `_id_counter` because `C0` does not allow global variables.


## Passing Accessibility Permissions

If partially verified function is called within fully verified function, then an `OwnedFields` struct must be created to collect the permissions that are availble to fully verified functionand pass them to partially verified function for use in runtime checks.

There are three types of partially verified functions. A function is fully imprecise if both its precondition and postcondition are imprecise. A function is partially imprecise if only one of its precondition or postcondition is imprecise. Fully imprecise functions are passed the entire `OwnedFields` struct without modification. However, partially imprecise functions require additional handling.

### Imprecise Precondition, Precise Postcondition

If a precondition is imprecise, then `OwnedFields` will be passed in without modification. However, the precise postcondition indicates that only a subset of field access permissions will be returned to the caller. This is accomplished by replacing the current `OwnedFields` struct with a new one that contains only the specified permissions.

```
void example(Node* node, OwnedFields** fields) {
    //@requires ?;
    //@ensures acc(node->value);
    
    ...

    *fields = alloc(OwnedFields);
    initOwnedFields(*fields);
    inherit(*fields, node->_id, ["value"]);
}
```

### Precise Precondition, Imprecise Postcondition

For functions with precise preconditions and imprecise postconditions, a secondary `OwnedFields` struct is created before the function is called and passed as a parameter. After function returns, the secondary `OwnedFields` is combined with the preexisting one via a call to `merge`.

```

void call_example(Node* node){
    //@requires true;
    //@ensures true;

    OwnedFields * fields = alloc(OwnedFields);
    initOwnedFields(fields);
    inherit(fields, node->_id, ["value", "next"]);

    ...

    OwnedFields* fields_1 = alloc(OwnedFields);
    initOwnedFields(fields_1);
    inherit(fields_1, node->_id, ["value", "next"]);

    example(&fields_1);

    merge(fields, fields_1);

}
void example(Node* node, OwnedFields** fields){
    //@requires acc(node->value) * acc(node->next);
    //@ensures ?;
    ...
}

```

The `merge` function takes the union of two sets of permissions and assigns them to the first set.

## Inserting Runtime Checks
Each runtime check is represented as a tuple `(✅, 🏳, 📖)`, where ✅ is the check that must occur, 🏳 is a flag indicating if the check possibly overlaps with another memory location, and 📖 is the context which the check was derived from. 

If a field access check doesn't overlap, then only a call to `assertAcc` is necessary:

```
int getValue(Node* node, OwnedFields* fields){
    //@requires ?
    //@ensures ?

    assertAcc(fields, node->_id, ["value"]);
    return node->value;
}
```
The `assertAcc` function has no effect if the given field is included in the current `OwnedFields` struct, and will terminate execution otherwise. 

When multiple accessibility predicates are joined by the separating conjunction, then it is necessary to ensure that none of the predicates use different aliases to the same memory location. This can be accomplished by temporarily removing an accessibility permission from the set with a call to `mask`. 

Once the check is complete, `unmask` is called, which unmasks all previously hidden accessibility permissions as is necessary for use in additional runtime checks or calls to imprecise methods that occur after the given runtime check. 

If the runtime accessibility check was derived from a context that includes statically verified accessibility predicates, then this static component is also hidden via `mask` prior to the runtime checks.