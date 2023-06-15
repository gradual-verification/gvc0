dskk

# This is a single-line comment

#This is another single-line comment

#@predicate orderedListSegWithPrev(struct Node *start, struct Node *end, int prev, int endVal);

"""
    This is a multi-line comment
"""

"""This is also a multi-line comment"""

""" comment: requires true; """

"""@
predicate orderedListSegWithPrev(struct Node *start, struct Node *end, int prev, int endVal) =
    (start == end) ?
        ( (end == NULL) ? true : endVal >= prev )
        :
        (
             acc(start->val) && acc(start->next) && acc(start->deleted) &&
            start->val >= prev && orderedListSegWithPrev(start->next, end, start->val, endVal)
        ) ;
@"""