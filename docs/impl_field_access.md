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

If a fully verified function allocates memory but doesn't call a partially verified function, it will be passed `_id_counter` as a parameter and new structs will be assigned an ID directly.
```
Node * node = alloc(Node);
node->_id = *(_id_counter)++;
```
It is necessary to pass `_id_counter` because `C0` does not allow global variables.

## Passing Accessibility Permissions

If a fully verified function calls a partially verified function, then an `OwnedFields` struct must be created to collect the permissions that are availble at the beginning of the fully verified function and pass them to partially verified function.

Partially verified functions are differentiated based on the precision of their specifications. A partially verified function is **fully imprecise** if both its precondition and postcondition are imprecise, and it is **partially imprecise** if only one is imprecise. Fully imprecise functions are passed the entire `OwnedFields` struct without modification. However, partially imprecise functions require additional handling at call sites and returns.

### Imprecise Precondition, Precise Postcondition

If a partially verified function's precondition is imprecise, then `OwnedFields` will be passed in without modification. However, the function's precise postcondition indicates that only a subset of field access permissions will be returned to the caller. This is accomplished by replacing the current `OwnedFields` struct with a new one that contains only the specified permissions. A call to `inherit` adds an existing struct instance the specified fields to the accessibility set.

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

For partially verified functions with precise preconditions and imprecise postconditions, a secondary `OwnedFields` struct is created before the function is called and passed as a parameter. After function returns, the secondary `OwnedFields` is combined with the preexisting one via a call to `merge`.

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
    //@requires ?;
    //@ensures ?;

    assertAcc(fields, node->_id, ["value"]);
    return node->value;
}
```
The `assertAcc` function has no effect if the field is accessible, but it will terminate execution if not.

When multiple accessibility predicates are joined by the separating conjunction, it is necessary to ensure that none of the predicates use different aliases to the same memory location. Consider the following function:

```
void call_example(Node* x, Node* y){
    //@requires ? && acc(x.value);
    //@ensures ?;

    int sum = x->value + y->value;

    example(x);
    ...
}
void example(Node* a){
    //@requires ?
    //@ensures ?
    ...
}

```
Note that `x.f` has been statically verified, but `y.f` has not been, and a runtime check must be inserted to satisfy the `assert` statement. 
Only the accessibility of `x.f` has been statically ensured; it might be an alias for `y.f`. To satisfy the separating conjunction (`&&`), we must ensure that `y.f` is a separate heap location.

This could be accomplished by removing the accessibility permission for `x.f` from the set before `assert` is called. However, it is necessary to retain the permission for `x.f` so that it can be passed to the partially verified function `example`.  

To temporarily hide a permission, a call to `mask` is injected. Calling `unmask` unhides the permission for use later on.  
```
void call_example(Node* x, Node* y, OwnedFields ** fields){
    //@requires ? && acc(x.f);
    //@ensures ?;
    
    mask(*fields, x->_id, ["value"]);
    assertAcc(fields, y->_id, ["value"]);

    unmask(*fields, x->_id, ["value"]);

    example(x, fields);
    ...
}

void example(Node* a, OwnedFields ** fields){
    //@requires ?
    //@ensures ?
    ...
}
```