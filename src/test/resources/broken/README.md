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

> **(C.1)** A plausible mistake someone could make while implementing composite is with the main property defined in `fixup_ancestors`. The user could assume that we just want to update the `parentTotal` by the `right` and `left` totals, but if we didn't add anything to the totals, we would still need `parentTotal = 1`, which leads to the following implementation mistake:

```diff
int fixup_ancestors(struct Node *node, struct Node *parent, int oldTotal, int newTotal)
-  //@ requires context(node, parent, oldTotal);
+  //@ requires ?;
  //@ ensures context(node, parent, newTotal);
{
- //@ unfold context(node, parent, oldTotal);
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

-    int parentTotal = 1 + leftTotal + rightTotal;
+    int parentTotal = leftTotal + rightTotal;
    parent->total = parentTotal;
    fixup_ancestors(parent, grandparent, oldparentTotal, parentTotal);
  }
- //@ fold context(node, parent, newTotal);
  return 0;
}
```

> **(C.2)** Following the previous example, we can just remove `fixup_ancestors` altogether from the add methods `tree_add_left` and `tree_add_right`.

```diff
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

## `--check` output 

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

## `--dynamic` output 

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
sbt:gvc0> run "./src/test/resources/broken/composite_1.c0"
[info] running (fork) gvc.Main ./src/test/resources/broken/composite_1.c0
[info] [*] — Mon Sep 26 06:25:04 EDT 2022
[success] Total time: 12 s, completed Sep 26, 2022, 6:25:15 AM
sbt:gvc0> run "./src/test/resources/broken/composite_1.c0" --dynamic
[info] running (fork) gvc.Main ./src/test/resources/broken/composite_1.c0 --dynamic
[info] [*] — Mon Sep 26 06:25:19 EDT 2022
[error] Exception in thread "main" gvc.benchmarking.Timing$CC0ExecutionException: c0rt: /home/jpvinnie/Documents/uni/CMU/src/gradual/gvc0/./src/test/resources/broken/composite_1.verified.c0: 344.9-344.44: assert failed11
[error]         at gvc.benchmarking.Timing$.execNonzero$1(Timing.scala:159)
[error]         at gvc.benchmarking.Timing$.$anonfun$execTimed$1(Timing.scala:162)
[error]         at gvc.benchmarking.Timing$.$anonfun$execTimed$1$adapted(Timing.scala:162)
[error]         at gvc.benchmarking.Timing$.$anonfun$runTimedCommand$3(Timing.scala:129)
[error]         at gvc.benchmarking.Timing$.$anonfun$runTimedCommand$3$adapted(Timing.scala:121)
[error]         at scala.collection.immutable.Range.foreach(Range.scala:158)
[error]         at gvc.benchmarking.Timing$.runTimedCommand(Timing.scala:121)
[error]         at gvc.benchmarking.Timing$.execTimed(Timing.scala:162)
[error]         at gvc.Main$.$anonfun$run$1(main.scala:97)
[error]         at gvc.benchmarking.Output$.printTiming(Output.scala:39)
[error]         at gvc.Main$.run(main.scala:86)
[error]         at gvc.Main$.delayedEndpoint$gvc$Main$1(main.scala:73)
[error]         at gvc.Main$delayedInit$body.apply(main.scala:42)
[error]         at scala.Function0.apply$mcV$sp(Function0.scala:39)
[error]         at scala.Function0.apply$mcV$sp$(Function0.scala:39)
[error]         at scala.runtime.AbstractFunction0.apply$mcV$sp(AbstractFunction0.scala:17)
[error]         at scala.App.$anonfun$main$1$adapted(App.scala:80)
[error]         at scala.collection.immutable.List.foreach(List.scala:431)
[error]         at scala.App.main(App.scala:80)
[error]         at scala.App.main$(App.scala:78)
[error]         at gvc.Main$.main(main.scala:42)
[error]         at gvc.Main.main(main.scala)
[error] Nonzero exit code returned from runner: 1
[error] (Compile / run) Nonzero exit code returned from runner: 1
[error] Total time: 2 s, completed Sep 26, 2022, 6:25:20 AM
```

> 2

```
sbt:gvc0> run "./src/test/resources/broken/composite_2.c0" 
[info] running (fork) gvc.Main ./src/test/resources/broken/composite_2.c0
[info] [*] — Mon Sep 26 05:39:48 EDT 2022
[success] Total time: 8 s, completed Sep 26, 2022, 5:39:55 AM
sbt:gvc0> run "./src/test/resources/broken/composite_2.c0" --dynamic
[info] running (fork) gvc.Main ./src/test/resources/broken/composite_2.c0 --dynamic
[info] [*] — Mon Sep 26 05:40:00 EDT 2022
[error] Exception in thread "main" gvc.benchmarking.Timing$CC0ExecutionException: c0rt: /home/jpvinnie/Documents/uni/CMU/src/gradual/gvc0/./src/test/resources/broken/composite_2.verified.c0: 344.9-344.44: assert failed11
[error]         at gvc.benchmarking.Timing$.execNonzero$1(Timing.scala:159)
[error]         at gvc.benchmarking.Timing$.$anonfun$execTimed$1(Timing.scala:162)
[error]         at gvc.benchmarking.Timing$.$anonfun$execTimed$1$adapted(Timing.scala:162)
[error]         at gvc.benchmarking.Timing$.$anonfun$runTimedCommand$3(Timing.scala:129)
[error]         at gvc.benchmarking.Timing$.$anonfun$runTimedCommand$3$adapted(Timing.scala:121)
[error]         at scala.collection.immutable.Range.foreach(Range.scala:158)
[error]         at gvc.benchmarking.Timing$.runTimedCommand(Timing.scala:121)
[error]         at gvc.benchmarking.Timing$.execTimed(Timing.scala:162)
[error]         at gvc.Main$.$anonfun$run$1(main.scala:97)
[error]         at gvc.benchmarking.Output$.printTiming(Output.scala:39)
[error]         at gvc.Main$.run(main.scala:86)
[error]         at gvc.Main$.delayedEndpoint$gvc$Main$1(main.scala:73)
[error]         at gvc.Main$delayedInit$body.apply(main.scala:42)
[error]         at scala.Function0.apply$mcV$sp(Function0.scala:39)
[error]         at scala.Function0.apply$mcV$sp$(Function0.scala:39)
[error]         at scala.runtime.AbstractFunction0.apply$mcV$sp(AbstractFunction0.scala:17)
[error]         at scala.App.$anonfun$main$1$adapted(App.scala:80)
[error]         at scala.collection.immutable.List.foreach(List.scala:431)
[error]         at scala.App.main(App.scala:80)
[error]         at scala.App.main$(App.scala:78)
[error]         at gvc.Main$.main(main.scala:42)
[error]         at gvc.Main.main(main.scala)
[error] Nonzero exit code returned from runner: 1
[error] (Compile / run) Nonzero exit code returned from runner: 1
[error] Total time: 2 s, completed Sep 26, 2022, 5:40:01 AM
```

> 3

```

```

> 4

```

```