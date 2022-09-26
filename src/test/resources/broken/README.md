# Broken examples 
For these broken examples, we are using the files found in `quant-study`. When breaking examples, we want to take into consideration the following:

- Modify specification so proofs are done dynamically instead of statically
- Put as much imprecision as possible but make sure you're still proving something

The first two examples of each program have implementation errors, and the following two are specification errors. 

Details for each example can be found [here](https://github.com/gradual-verification/recursive-predicates/wiki).

## Implementation 
**For breaking implementations, we want to make sure that the code breaks during dynamic verification and not just a static fail. This requires all methods changed to remove `folds`/`unfolds` and preconditions must stay unspecified.**

### BST

> **(A.1)** We first want to break the tree order, the left subtree has to be less than the right subtree. Therefore, we insert a node which is greater in the left hand side of the tree. (Remember we remove `folds`/`unfolds`)

```diff
-    if (x < v) {
+    if (v < x) {
      if (l != NULL) {
        root->left = tree_add_helper(l, x, min, v-1);
      } else {
        root->left = create_tree_helper(x, min, v-1);
      }
    } else {
-     if (v < x) {
+     if (x < v) {
        if (r != NULL) {
          root->right = tree_add_helper(r, x, v+1, max);
        } else {
          root->right = create_tree_helper(x, v+1, max);
        }
      }
   }
```

> **(A.2)** Interestingly, BST is forced to define the max and min int values in C for adding and removing in a tree. A trivial error is to invert these values

```diff
struct Node *tree_add(struct Node *root, int x)
-  //@ requires tree(root) && -2147483647 <= x && x <= 2147483647;
+  //@ requires ?;
  //@ ensures tree(\result);
{
-  struct Node *res = tree_add_helper(root, x, -2147483647, 2147483647);
+  struct Node *res = tree_add_helper(root, x, 2147483647, -2147483647);
  return res;
}
```

---

### List 

> **(B.1)** We can mess with `list_insert`, and remove the edge cases for dealing with `NULL` lists. (Remember we remove all `folds` and `unfolds`).

```diff
struct Node *list_insert(struct Node *list, int val)
-  //@ requires sorted(list);
+  //@ requires ?;
  //@ ensures sorted(\result);
{
-  if (list == NULL || val <= list->val) {
+  if (val <= list->val) {
...
-    while (curr->next != NULL && curr->next->val < val)
+    while (curr->next->val < val)
...
int main()
  //@ requires true;
  //@ ensures true;
{
  int stress = 0;
  struct Node *l = create_list(3);
  int i = 0;
  while(i < stress)
  //@loop_invariant 0 <= i && i <= stress;
  {
    l = list_insert(l, 1);
    i += 1;
  }
+  l = list_insert(NULL, 1);
  return 0;
}
```

> **(B.2)** Following the previous example, we can make a mistake on one of the branches for `list_insert`, if `stress = 1` we should get the error from running with `-x` rather than `--dynamic`:

```diff
-  if (list == NULL || val <= list->val) {
+  if (list == NULL) {
```

---

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

### BST

> **(A.3)** We follow the bst implementation break of changing the max and min values, and the program should recognize that the precondition for `add` does not hold

```diff
struct Node *tree_add(struct Node *root, int x)
-  //@ requires tree(root) && -2147483647 <= x && x <= 2147483647;
+  //@ requires ? && 2147483647 <= x && x <= -2147483647;
  //@ ensures tree(\result);
{
  struct Node *res = tree_add_helper(root, x, -2147483647, 2147483647);
  return res;
}
```

> **(A.4)** Similarly, we can change the min max order in the `add_helper` precondition instead, and unspecify preconditions in `add` and `remove`.

```diff
struct Node *tree_add_helper(struct Node *root, int x, int min, int max)
-  //@ requires bst(root, min, max) && min <= x && x <= max;
+  //@ requires ? && max <= x && x <= min;
  //@ ensures bst(\result, min, max);
```

---

### List 

> **(B.3)** 

```diff

```

> **(B.4)**

```diff

```

---

### Composite

> **(C.3)** 

```diff

```

> **(C.4)**

```diff

```

## `--dynamic` output 

### A.

> 1 (If we only change the precondition for `add_helper` then `-x` will error for not holding the precondition for `add` and `remove`)

```
sbt:gvc0> run "./src/test/resources/broken/bst_1.c0" -x
[info] running (fork) gvc.Main ./src/test/resources/broken/bst_1.c0 -x
[info] [*] — Mon Sep 26 08:09:31 EDT 2022
[error] c0rt: ./src/test/resources/broken/bst_1.verified.c0: 331.11-331.32: assert failed
[error] Nonzero exit code returned from runner: 134
[error] (Compile / run) Nonzero exit code returned from runner: 134
[error] Total time: 5 s, completed Sep 26, 2022, 8:09:35 AM
```

> 2

```
sbt:gvc0> run "./src/test/resources/broken/bst_1.c0" -x
[info] running (fork) gvc.Main ./src/test/resources/broken/bst_1.c0 -x
[info] [*] — Mon Sep 26 08:16:59 EDT 2022
[error] c0rt: ./src/test/resources/broken/bst_1.verified.c0: 331.11-331.32: assert failed
[error] Nonzero exit code returned from runner: 134
[error] (Compile / run) Nonzero exit code returned from runner: 134
[error] Total time: 5 s, completed Sep 26, 2022, 8:17:03 AM
sbt:gvc0> run "./src/test/resources/broken/bst_2.c0" --dynamic
[info] running (fork) gvc.Main ./src/test/resources/broken/bst_2.c0 --dynamic
[info] [*] — Mon Sep 26 08:17:06 EDT 2022
[error] Exception in thread "main" gvc.benchmarking.Timing$CC0ExecutionException: c0rt: /home/jpvinnie/Documents/uni/CMU/src/gradual/gvc0/./src/test/resources/broken/bst_2.verified.c0: 137.5-137.30: assert failed11
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
[error] Total time: 1 s, completed Sep 26, 2022, 8:17:07 AM
```

> 3

```
sbt:gvc0> run "./src/test/resources/broken/bst_3.c0" -x
[info] running (fork) gvc.Main ./src/test/resources/broken/bst_3.c0 -x
[info] [*] — Mon Sep 26 08:29:25 EDT 2022
[error] Exception in thread "main" gvc.VerificationException: The precondition of method tree_add might not hold. Assertion 2147483647 <= toAdd might not hold. (<no position>)
[error]         at gvc.Main$.verifySiliconProvided(main.scala:293)
[error]         at gvc.Main$.verify(main.scala:255)
[error]         at gvc.Main$.$anonfun$run$5(main.scala:148)
[error]         at gvc.benchmarking.Output$.printTiming(Output.scala:39)
[error]         at gvc.Main$.run(main.scala:147)
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
[error] Total time: 5 s, completed Sep 26, 2022, 8:29:29 AM
sbt:gvc0> run "./src/test/resources/broken/bst_3.c0" --dynamic
[info] running (fork) gvc.Main ./src/test/resources/broken/bst_3.c0 --dynamic
[info] [*] — Mon Sep 26 08:29:38 EDT 2022
[error] Exception in thread "main" gvc.benchmarking.Timing$CC0ExecutionException: c0rt: /home/jpvinnie/Documents/uni/CMU/src/gradual/gvc0/./src/test/resources/broken/bst_3.verified.c0: 342.3-342.27: assert failed11
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
[error] Total time: 2 s, completed Sep 26, 2022, 8:29:39 AM
```

> 4

```

```

---

### B.

> 1

```
sbt:gvc0> run "./src/test/resources/broken/list_1.c0" --dynamic
[info] running (fork) gvc.Main ./src/test/resources/broken/list_1.c0 --dynamic
[info] [*] — Mon Sep 26 06:54:20 EDT 2022
[error] Exception in thread "main" gvc.benchmarking.Timing$CC0ExecutionException: 11
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
[error] Total time: 1 s, completed Sep 26, 2022, 6:54:20 AM
```

> 2

```
sbt:gvc0> run "./src/test/resources/broken/list_2.c0" -x
[info] running (fork) gvc.Main ./src/test/resources/broken/list_2.c0 -x
[info] [*] — Mon Sep 26 07:56:51 EDT 2022
[error] c0rt: ./src/test/resources/broken/list_2.verified.c0: 145.7-145.32: assert failed
[error] Nonzero exit code returned from runner: 134
[error] (Compile / run) Nonzero exit code returned from runner: 134
[error] Total time: 13 s, completed Sep 26, 2022, 7:57:04 AM
```

> 3

```

```

> 4

```

```

---

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

---

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

---

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