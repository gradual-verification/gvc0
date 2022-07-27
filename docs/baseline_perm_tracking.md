# Baseline Permission Tracking

Every method takes a set of permissions as a parameter, which I refer to here as the global set.

## Preconditions

If the precondition of a method is precise, create a set of permissions containing only what is given by the
precondition (context set). This is done in a single evaluation of the precondition where we check that the permissions
are present in the global set, add them to the context set, and then remove them from the global set. Use the context
set for all checking in the body of the function, passing it as the global set to method calls.

If the precondition is imprecise, check that its permissions are present in the global set. Use the global set for all
checking in the body of the function.

## Postconditions

If the precondition was precise, but the postcondition is imprecise, then join the context set with the global set. If
both the precondition and the postcondition are precise, then check that all permissions given by the postcondition are
present in the context set, and add these to the global set.

If both the precondition and postcondition are imprecise, just validate the postcondition without doing any
addition/removal of permissions and return.

## Note:

The framing check version of the baseline does all of the permission tracking operations above without actually
validating that the permissions in the precondition and postcondition are present in a particular set. (edited) 