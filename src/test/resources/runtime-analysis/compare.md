# Comparison for runtime checks 

### `appendLemmaBody` pre-/post-conditions with dynamic checks (specifically no `segSortedHelper`)

**Before**:

```c
while (curr->next != NULL && curr->next->val < val)
{
  prev = curr;
  curr = prev->next;
  if (list == prev)
  {
  }
  else
  {
    appendLemmaLoopBody(list->next, prev, curr, list->val, prev->val, prev->val, curr->val, _instanceCounter);
  }
}
```

**After**:

```c
    while (curr->next != NULL && curr->next->val < val)
    {
      prev = curr;
      curr = prev->next;
      _cond_7 = list == prev;
      _cond_8 = curr == curr;
      _cond_9 = curr == NULL;
      _cond_10 = list == prev;
      if (list == prev)
      {
      }
      else
      {
        _cond_11 = prev == curr;
        _cond_12 = curr == NULL;
        appendLemmaLoopBody(list->next, prev, curr, list->val, prev->val, prev->val, curr->val, _ownedFields);
        _cond_13 = curr == NULL;
      }
      if (!_cond_1 && ... && !(list == curr))
      {
        assertAcc(_ownedFields, list != NULL ? list->_id : -1, 0, "Field access runtime check failed for struct Node.val");
        assertAcc(_ownedFields, list != NULL ? list->_id : -1, 1, "Field access runtime check failed for struct Node.next");
      }
      if (!_cond_1 && ... && !(list == curr))
      {
        sortedSegHelper(list->next, curr, list->val, curr->val, _ownedFields);
      }
      _cond_15 = list == curr;
      if (!_cond_1 && ... && !_cond_15)
      {
        assertAcc(_ownedFields, curr != NULL ? curr->_id : -1, 1, "Field access runtime check failed for struct Node.next");
        assertAcc(_ownedFields, curr != NULL ? curr->_id : -1, 0, "Field access runtime check failed for struct Node.val");
      }
      _cond_16 = !(curr == NULL) && curr->next == NULL;
      _cond_17 = true;
      _tempFields = initOwnedFields(_ownedFields->instanceCounter);
      if (!_cond_1 && ... && !(curr->next == NULL))
      {
        assertAcc(_ownedFields, curr->next != NULL ? curr->next->_id : -1, 0, "Field access runtime check failed for struct Node.val");
        assertAcc(_ownedFields, curr->next != NULL ? curr->next->_id : -1, 1, "Field access runtime check failed for struct Node.next");
      }
      if (!_cond_1 && ... && _cond_17)
      {
        assert(curr->val <= val);
        sortedSeg(list, curr, curr->val, _ownedFields);
      }
      if (!_cond_1 && ... && !(curr->next == NULL))
      {
        sortedSegHelper(curr->next->next, NULL, curr->next->val, -1, _ownedFields);
      }
      addAccEnsureSeparate(_tempFields, curr != NULL ? curr->_id : -1, 0, 3, "Overlapping field permissions for struct Node.val");
      addAccEnsureSeparate(_tempFields, curr != NULL ? curr->_id : -1, 1, 3, "Overlapping field permissions for struct Node.next");
      sep_sortedSeg(list, curr, curr->val, _tempFields);
      if (!(curr->next == NULL))
      {
        addAccEnsureSeparate(_tempFields, curr->next != NULL ? curr->next->_id : -1, 1, 3, "Overlapping field permissions for struct Node.next");
        addAccEnsureSeparate(_tempFields, curr->next != NULL ? curr->next->_id : -1, 0, 3, "Overlapping field permissions for struct Node.val");
        sep_sortedSegHelper(curr->next->next, NULL, curr->next->val, -1, _tempFields);
      }
    }
```

---