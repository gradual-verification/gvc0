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

If a fully verified function calls a partially verified function, then an `OwnedFields` struct must be created to collect the permissions that are available at the beginning of the fully verified function and pass them to partially verified function. These permissions are obtained by examining the function's specifications and receiving information from the verifier, and are added to `OwnedFields` immediately after initialization via injected calls to `inherit`.

```
void example(Node* n){
    //@requires acc(n.value) && acc(n.next)
    //@ensures acc(n.next)

    OwnedFields* fields = alloc(OwnedFields);
    initOwnedFields(*fields);

    inherit(fields, n->_id, ["value", "next"]);

    ...
}
```

Partially verified functions are differentiated based on the precision of their specifications. A partially verified function is **fully imprecise** if both its precondition and postcondition are imprecise, and it is **partially imprecise** if only one is imprecise. Fully imprecise functions are passed the entire `OwnedFields` struct without modification. However, partially imprecise functions require additional handling at call sites and returns.

### Imprecise Precondition, Precise Postcondition

If a function's precondition is imprecise, then `OwnedFields` will be passed in without modification. However, if it's postcondition is precise, then only a subset of the field access permissions must be returned to the caller. This is accomplished by replacing the current `OwnedFields` struct with a new one that contains only the specified permissions. A call to `inherit` adds an existing struct instance and the specified fields to the accessibility set.

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
Each runtime check is represented as a tuple containing the check itself, a flag indicating whether the check might overlap with statically verified fields, and the context in which the check occurs. Note that the context is derived from the current functions static specifications and information from the verifier, similar to what occurs when `OwnedFields` is initialized.

If a field access check doesn't overlap, then runtime checks can be discharged without any extra handling. To verify that a field is accessible, `assertAcc` is called:

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
Only the accessibility of `x.value` has been statically ensured; it might be an alias for `y.value`. To satisfy the separating conjunction (`&&`), we must ensure that `y.value` is a separate heap location.

This can be accomplished by removing the accessibility permission for `x.value` from `OwnedFields` before `assert` is called. However, it is necessary to retain the permission for `x.value` so that it can be passed to the partially verified function `example`.  

To temporarily hide a permission, a call to `mask` is injected. Calling `unmask` unhides the permission for use later on.  
```
void call_example(Node* x, Node* y, OwnedFields ** fields){
    //@requires ? && acc(x.f);
    //@ensures ?;
    
    mask(*fields, x->_id, ["value"]);
    assertAcc(*fields, y->_id, ["value"]);

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

Any time that an accessibility check involves the separating conjunction, all previously verified permissions must be `mask`ed before the current permission can be verified. This procedure holds for cases when all conjuncts require runtime checks and when only a subset do. Statically verified permissions are identified by examining the context of the runtime check, and all are masked before the runtime check. When a runtime check involves two or more conjuncts, each conjunct is checked separately with interleaved calls to mask to ensure separation:

```
void example(Node* x, Node* y, OwnedFields** fields){
    //@requires ?;
    //@ensures ?;

    assertAcc(*fields, x->_id, ["value"]);
    
    mask(*fields, x->_id, ["value"]);

    assertAcc(*fields, y->_id, ["value"]);
    
    unmask(*fields, x->_id, ["value]);

    int sum = x->value + y->value;
    ...
}
```