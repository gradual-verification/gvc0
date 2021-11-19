# Runtime Checks for Field Access Predicates

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

If a fully verified function calls a partially verified function, then an `OwnedFields` struct must be created to collect the permissions that are available at the beginning of the fully verified function and pass them to partially verified function. These permissions are obtained by examining the function's specifications and receiving information from the verifier, and they are added to `OwnedFields` immediately after initialization via injected calls to `inherit`.

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

For partially verified functions with precise preconditions and imprecise postconditions, a secondary `OwnedFields` struct is created before the function is called and receives all permissions from the first one via a call to `merge`. It is passed as a parameter, and after the function returns, the secondary `OwnedFields` is combined with the preexisting one with another call to `merge`.

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

    merge(fields_1, fields);

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
Each runtime check is represented as a tuple containing the check itself, a flag indicating whether the check might overlap with statically verified field, and the context in which the check occurs. For an unverified field to "overlap" with a statically verified field means that there is a possibility that both fields are aliases to the same heap location. Additionally, note that the context for a runtime check is derived from the current function's static specifications and information from the verifier, similar to what occurs when `OwnedFields` is initialized in a fully verified function.

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

When multiple accessibility predicates are joined by the separating conjunction, it is necessary to ensure that none of the predicates use different aliases to the same memory location. This is guaranteed to occur if the runtime checks overlap, but also can occur with no overlap if the runtime check includes multiple conjoined accessibiliy predicates. Consider the following function:

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

To temporarily hide a permission, a call to `mask` is injected. Calling `unmask` unhides all previously `mask`ed permissions so that they can be available later on. 
```
void call_example(Node* x, Node* y, OwnedFields ** fields){
    //@requires ? && acc(x.value);
    //@ensures ?;
    
    mask(*fields, x->_id, ["value"]);
    assertAcc(*fields, y->_id, ["value"]);

    unmask(*fields);

    example(x, fields);
    ...
}

void example(Node* a, OwnedFields ** fields){
    //@requires ?
    //@ensures ?
    ...
}
```
Any time that an accessibility check involves the separating conjunction, all previously verified permissions must be `mask`ed before the current permission can be verified. This procedure holds for cases when all conjuncts require runtime checks and when only a subset do. Statically verified permissions are identified by examining the context of the runtime check, and all are masked before the check is executed. When a runtime check involves two or more conjuncts, each conjunct is checked independently with interleaved calls to mask to ensure separation:

```
void example(Node* x, Node* y, OwnedFields** fields){
    //@requires ?;
    //@ensures ?;

    assertAcc(*fields, x->_id, ["value"]);
    
    mask(*fields, x->_id, ["value"]);

    assertAcc(*fields, y->_id, ["value"]);
    
    unmask(*fields);

    int sum = x->value + y->value;
    ...
}
```

## Abstract Predicates

Abstract predicates are treated equirecursively during static verification, meaning that some accessibility permissions may be present, but hidden within the definition of the predicate. As such all abstract predicates present in runtime checks or sets of statically available permissions must be unfolded competely to ensure soundness.

To add these hidden permissions to `OwnedFields`, the compiler unfolds the predicate in its entirety and collects all accessibility permissions within. In cases where the predicate was statically verified, no checking is needed. However, when the predicate is involved in a runtime check, additional handling is necessary to satisfy any conditionals and separated conjuncts. 

Consider the following predicates:

```
predicate acyclic (List l) = acc(l.head) && listSeg(l.head, NULL);

predicate listSeg (Node from, Node to) =
    if (from == to) then true else
    acc(from.val) && acc(from.next) && listSeg(from.next, to)
```

A statically specified function calls an `imprecise` function, and it has `acyclic(l)` as a statically verified precondition.

```
void traverse(List l, Node* node){
    //@requires acyclic(l);

    unfold acyclic(l);
    
    Node current = l.head;

    while(current != NULL){
        //@loop_invariant current != NULL
        
        imprecise(current.value)
        
        current = current.next;
    }

            ...
}
```
Because of the imprecise function, an `OwnedFields` struct must be create, intialized with all accessibility permissions available to `printList`, and passed to `imprecise`. However, all of `printList`'s permissions are hidden in `acyclic`. To dynamically unfold `acyclic`, it is translated into a `c0` function. If the predicate has been statically verified, then permissions are collected for each `acc` within `acyclic` without any additional checking, because it is safe to assume that the separating conjunction is satisfied.

```
void acyclic(List l, OwnedFields* fields){
    inherit(fields, l._id, ["head"]);       // acc(l.head)
    listSeg(l.head, NULL, fields);
}

void listSeg(Node from, Node to, OwnedFields* fields){
    if(from == to){
        return true;
    }else{
        inherit(fields, from._id, ["val", "next"]);
        listSeg(from.next, to, fields);
    }
}
```

If a predicate is part of a runtime check, then `mask` and `assertAcc` must be used in place of each `acc` to satisfy the separating conjunction.

```
void acyclic(List l, OwnedFields* fields){
    assertAcc(fields, l._id, ["head"]);

    mask(fields, l._id, ["head]);

    listSeg(l.head, NULL, fields);
}

void listSeg(Node from, Node to, OwnedFields* fields){
    if(from == to){
        return;
    }else{
        assertAcc(fields, from._id, ["val"]);
        mask(fields, from._id, ["val"]);

        assertAcc(fields, from._id, ["next"]);
        mask(fields, from._id, ["next"]);

        listSeg(from.next, to, fields);
    }
}

```
In either case, the transformed predicate functions via its side effects of initializing permissions or aborting execution when a permission isn't present. A return value isn't necessary. As shown previously, once the runtime check completes, `unmask` is called to ensure that all permissions are available later on.
