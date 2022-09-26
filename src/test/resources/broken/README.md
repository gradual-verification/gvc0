# Broken examples 

## Implementation 
**For breaking implementations, we want to make sure that the code breaks during dynamic verification and not just a static fail. This requires all methods changed to remove `folds`/`unfolds` and preconditions must stay unspecified.**

### BST

> **(A.1)** We first want to break the tree order, the left subtree has to be less than the right subtree. Therefore, we insert a node which is greater in the left hand side of the tree.

```c

```

> **(A.2)**

```c

```

### List 

> **(B.1)** 

```c

```

> **(B.2)**

```c

```

### Composite 

> **(C.1)** 

```c

```

> **(C.2)** Composite's invariant is in `fixup_ancestors`, thefore a trivial implementation change is removing the invariant from the add methods `tree_add_left` and `tree_add_right`.

```diff
int fixup_ancestors(struct Node *node, struct Node *parent, int oldTotal, int newTotal)
- //@ requires context(node, parent, oldTotal);
+ //@ requires ?;
  //@ ensures context(node, parent, newTotal);
{
  //@ unfold context(node, parent, oldTotal);
  if (parent == NULL) {
  } else {
    struct Node *left = parent->left;
    struct Node *right = parent->right;
    struct Node *grandparent = parent->parent;
    int oldparentTotal = parent->total;
    int leftTotal = 0;
    int rightTotal = 0;
    if (node == left) {
      leftTotal = newTotal;
      if (right != NULL) {
        rightTotal = right->total;
      }
    } else {
      if (left != NULL) {
        leftTotal = left->total;
      }
      rightTotal = newTotal;
    }

    int parentTotal = 1 + leftTotal + rightTotal;
    parent->total = parentTotal;
    fixup_ancestors(parent, grandparent, oldparentTotal, parentTotal);
  }
  //@ fold context(node, parent, newTotal);
  return 0;
}

struct Node *tree_add_left(struct Node *node)
-  //@ requires tree(node);
+  //@ requires ?;
  //@ ensures tree(\result);
{
  //@ unfold tree(node);
  if (node == NULL) {
    //@ fold tree(node);
    return node;
  } else {
    struct Node *n = alloc(struct Node);
    n->left = NULL;
    n->right = NULL;
    n->parent = node;
    n->total = 1;
    //@ fold subtreeHelper(n->left, n->right, n, n->total);

    struct Node *nodeLeft = node->left;
    if (nodeLeft != NULL) {
      //@ fold tree(node);
      return node;
    } else {
-     //@ unfold subtreeHelper(nodeLeft, node->right, node, node->total);
      node->left = n;
-     //@ fold context(n, node, 0);
-     fixup_ancestors(n, node, 0, 1);
+     //fixup_ancestors(n, node, 0, 1);
-     //@ fold context(n, node, 0);      
      return n;
    }
  }
}

struct Node *tree_add_right(struct Node *node)
- //@ requires tree(node);
+ //@ requires ?;
  //@ ensures tree(\result);
{
  //@ unfold tree(node);
  if (node == NULL) {
    //@ fold tree(node);
    return node;
  } else {
    struct Node *n = alloc(struct Node);
    n->left = NULL;
    n->right = NULL;
    n->parent = node;
    n->total = 1;
    //@ fold subtreeHelper(n->left, n->right, n, n->total);

    struct Node *nodeRight = node->right;
    if (nodeRight != NULL) {
      //@ fold tree(node);
      return node;
    } else {
-     //@ unfold subtreeHelper(node->left, nodeRight, node, node->total);      
      node->right = n;
-     //@ fold context(n, node, 0);    
-     fixup_ancestors(n, node, 0, 1);
+    //fixup_ancestors(n, node, 0, 1);
-     //@ fold tree(n);      
      return n;
    }
  }
}
```

## Specifications 
**Similarly, we have to remove `folds`/`unfolds`, but we can't make preconditions just unspecified.**



### BFS

> **(A.3)** 

```c

```

> **(A.4)**

```c

```

### List 

> **(B.3)** 

```c

```

> **(B.4)**

```c

```

### Composite

> **(C.3)** 

```c

```

> **(C.4)**

```c

```

## `isValid` output 

### A.

> 1

```

```

> 2

```

```

> 3

```

```

> 4

```

```

### B.

> 1

```

```

> 2

```

```

> 3

```

```

> 4

```

```

### C.

> 1

```

```

> 2

```

```

> 3

```

```

> 4

```

```

## `-x` output 

### A.

> 1

```

```

> 2

```

```

> 3

```

```

> 4

```

```

### B.

> 1

```

```

> 2

```

```

> 3

```

```

> 4

```

```

### C.

> 1

```
sbt:gvc0> run "./src/test/resources/broken/composite_2.c0" -x
[info] running (fork) gvc.Main ./src/test/resources/broken/composite_2.c0 -x
[info] [*] — Mon Sep 26 04:31:07 EDT 2022
[error] c0rt: ./src/test/resources/broken/composite_2.verified.c0: 160.9-160.44: assert failed
[error] Nonzero exit code returned from runner: 134
[error] (Compile / run) Nonzero exit code returned from runner: 134
[error] Total time: 10 s, completed Sep 26, 2022, 4:31:17 AM
```

> 2

```

```

> 3

```

```

> 4

```

```