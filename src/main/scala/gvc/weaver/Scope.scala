package gvc.weaver

import gvc.transformer.IR

sealed trait Scope {
    // The containing method
    def method: IR.Method

    // The runtime checks that may occur within this scope
    def checks: List[RuntimeCheck]

    // The allocations that may occur within this scope
    def allocations: List[IR.AllocStruct]

    // The calls that may occur within this scope
    def calls: List[IR.Invoke]

    // Indicates whether this scope may require a dynamic permission set
    def requiresPerms: Boolean

    // Indicates whether this scope may modify a dynamic permission set
    def modifiesPerms: Boolean

    // Indicates whether this scope inherits the caller's dynamic permission
    // set. For example, a method with imprecise pre-condition.
    def inheritsPerms: Boolean

    // Indicates whether this scope returns a dynamic permission set. For
    // example, a method with imprecise post-condition. We assume that
    // `inheritsPerms` implies `returnsPerms`.
    def returnsPerms: Boolean

    // Scopes contained within this scope
    def children: List[LoopScope]

    // The block that syntactically represents this scope
    def block: IR.Block
  }

  trait MethodScope extends Scope {
    def block = method.body
  }

  trait LoopScope extends Scope {
    def op: IR.While

    def block = op.body
  }

