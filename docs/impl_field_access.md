The compiler maintains a mapping between indices and struct fields that corresponds to the order in which they appear in each struct definition. A unique `_id` field is injected into each struct definition.

```
struct Node {
    int val;                // index:   0
    struct Node* next;      //          1
    int _id;                //          2
};
```
To begin tracking field access, `main()` is injected with the following declaration and initialization:

```
int main() {
    OwnedFields * fields;
    initOwnedFields(fields);
    ...
}
```
When a new struct is allocated, a function call is injected so that `fields` can mark that the struct instance and its fields are accessible in the current stack frame.

```
Node * node = alloc(Node)
node->_id = addStruct(
    fields,     
    3,      //three fields within Node
    0       //called within main, stack frame 0
)

```
The function `addStruct` takes the number of fields available for the given struct, and returns a unique ID for that struct allocation. 

Additional tracking is required for fields that are pointers to other structs. 

```
Node * nextNode = alloc(Node);
...
node->next = nextNode;
trackStructWithin(
    fields,
    node->_id,
    1,              //id(node->next)
    nextNode->_id
)
```

OwnedFields will only track the instances and fields that are required for runtime checks or are used within the body of a function with an imprecise specification. 

Every function call that requires accessiblity runtime checks is injected with an `OwnedFields` parameter so that `fields` can always be accessible. Before a function is called, `fields` must account for the permissions that the function will acquire:

```
void printList(Node * head);
...

lowerStruct(fields, node->_id);
deleteNext(fields, node);
```

The function `lowerStruct` marks `node` and all of its fields as accessible in stackframe `n+1`. It will recurse when it encounters a field that is a pointer to another struct. Therefore, this will also provide `printList` with permissions to access `nextNode` via `node->next`. As desired, `lowerStruct` will trigger an exception if node is not available in the current stackframe. 

Each Field maintains the index of the stack frame at which it was most recently accessible, as well as a stack of prior indices where it was saved to a variable. Ever time a function call returns, if the permission for an accessible struct was not lost, then its accessibility index is decremented. If a permission for a struct is lost, then its index will be assigned to the top of its accessibility stack. If the stack is empty, then its index will be assigned to -1; the null stackframe. Consider the following pseudocode example:

```
Node* node;
Node* nextNode;
node->next = nextNode

foo(node){
    temp = node->next

    bar(node){
        temp = node;
        baz(node){
            ...
        }
        baz();
    }
    bar();
}
foo();

```
When `baz` is executed, the accessibility stack for `node` will be `[0, 2]`, and the stack for `nextNode` will be `[1]`. Both `node` and `nextNode` will be marked as accessible at stackframe index `3`. When `baz` returns, `node` will be marked as accessible at index `n-1 = 2`, but since the permission for `nextNode` was lost in `baz`, its accessibility level reverts to `1`, as it is at the top of `nextNode's` stack. An index is popped from the accessibiliy stack when the corresponding stackframe is popped.





