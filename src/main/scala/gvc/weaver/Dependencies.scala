package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR

// This helper class handles calculation of the permission requirements for a
// method; namely, whether a method requires permissions to be passed to it, and
// whether a method may produce permissions. This enables optimization in cases
// when calling an imprecise method that does not have acc runtime checks.

sealed trait ScopeDependencies {
  // The syntatic block that introduces this scope
  def block: IR.Block

  // The runtime checks that may occur within this scope
  def checks: Seq[RuntimeCheck]

  // The allocations that may occur within this scope
  def allocations: Seq[IR.AllocStruct]

  // The calls that may occur within this scope
  def calls: Seq[IR.Invoke]

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

  def children: Seq[WhileDependencies]
}

sealed trait MethodDependencies extends ScopeDependencies {
  def method: IR.Method
  def precisePre: Boolean
  def precisePost: Boolean
  def conditions: Iterable[TrackedCondition]

  def inheritsPerms: Boolean = !precisePre
  def returnsPerms: Boolean = !precisePost || !precisePre
}

sealed trait WhileDependencies extends ScopeDependencies {
  def op: IR.While
  def preciseInvariant: Boolean

  def inheritsPerms: Boolean = !preciseInvariant
  def returnsPerms: Boolean = !preciseInvariant
}

sealed trait ProgramDependencies {
  def program: IR.Program
  def methods: Map[String, MethodDependencies]
}

object Dependencies {

  // Helper class for determining equi-recursive precision
  private class EquirecursivePrecision(program: IR.Program) {
    private val predicatePrecision = mutable.HashMap[String, Boolean]()

    def isPrecise(pred: IR.Predicate): Boolean = {
      predicatePrecision.get(pred.name) match {
        case Some(v) => v
        case None => {
          predicatePrecision.update(pred.name, true)
          val result = isPrecise(pred.expression)
          predicatePrecision.update(pred.name, result)
          result
        }
      }
    }

    def isPrecise(e: IR.Expression): Boolean = e match {
      case _: IR.Imprecise => false
      case c: IR.Conditional => isPrecise(c.ifTrue) && isPrecise(c.ifFalse)
      case p: IR.PredicateInstance => isPrecise(p.predicate)
      case _ => true
    }

    def isPrecise(e: Option[IR.Expression]): Boolean = e match {
      case None => true
      case Some(e) => isPrecise(e)
    }
  }

  private sealed abstract class DependencyScope extends ScopeDependencies {
    val calls = mutable.ListBuffer[IR.Invoke]()
    val allocations = mutable.ListBuffer[IR.AllocStruct]()
    val permDependencies = mutable.HashSet[String]()
    val children = mutable.ListBuffer[WhileDependenciesImpl]()
    var requiresPerms = false
    var modifiesPerms = false
  }

  private class MethodDependenciesImpl(
    val method: IR.Method,
    val conditions: Iterable[TrackedCondition],
    val checks: Seq[RuntimeCheck],
    val precisePre: Boolean,
    val precisePost: Boolean
   ) extends DependencyScope with MethodDependencies {
    
    def block: IR.Block = method.body
  }

  private class WhileDependenciesImpl(
    val op: IR.While,
    val checks: Seq[RuntimeCheck],
    val preciseInvariant: Boolean)
    extends DependencyScope with WhileDependencies {

    def block: IR.Block = op.block
  }

  private class ProgramDependenciesImpl(
    val program: IR.Program,
    val methods: Map[String, MethodDependenciesImpl]
  ) extends ProgramDependencies

  def calculate(scope: ProgramScope): ProgramDependencies = {
    val program = scope.program
    val precision = new EquirecursivePrecision(program)

    val graph = scope.methods.map({ case (k, v) => (k, initDependencies(v, precision)) })
    val deps = new ProgramDependenciesImpl(program, graph)

    val collect = mutable.HashSet[String]()
    graph.values.foreach(c => {
      setRequiresPerms(c, deps, collect)
      setModifiesPerms(c, deps, collect)
    })

    deps
  }

  private def initDependencies(
    scope: MethodScope,
    precision: EquirecursivePrecision
  ): MethodDependenciesImpl = {
    val method = scope.method
    val dep = new MethodDependenciesImpl(
      method,
      scope.conditions,
      scope.checks,
      precision.isPrecise(method.precondition),
      precision.isPrecise(method.postcondition)
    )

    traverseBlock(method.body, dep)
    dep.children ++= scope.children.map(initDependencies(_, precision))

    dep.requiresPerms = requiresPerms(scope.checks)
    dep.modifiesPerms =
      if (dep.returnsPerms) !dep.allocations.isEmpty
      else refsPerms(method.precondition) || refsPerms(method.postcondition)

    dep
  }

  private def initDependencies(
    scope: WhileScope,
    precision: EquirecursivePrecision
  ): WhileDependenciesImpl = {
    val op = scope.op
    val dep = new WhileDependenciesImpl(
      op,
      scope.checks,
      precision.isPrecise(op.invariant)
    )

    traverseBlock(op.block, dep)
    dep.children ++= scope.children.map(initDependencies(_, precision))

    dep.requiresPerms = requiresPerms(scope.checks)
    dep.modifiesPerms =
      if (dep.preciseInvariant) refsPerms(dep.op.invariant)
      else !dep.allocations.isEmpty

    dep
  }

  private def traverseBlock(block: IR.Block, dep: DependencyScope) {
    // Note that we do not traverse into `while` statements, because we assume
    // that each `while` will have its own Scope instance
    block.foreach(_ match {
      case _: IR.AllocArray | _: IR.AllocValue =>
        throw new WeaverException("Unsupported allocation")
      case alloc: IR.AllocStruct =>
        dep.allocations += alloc
      case call: IR.Invoke =>
        dep.calls += call
      case cond: IR.If => {
        traverseBlock(cond.ifTrue, dep)
        traverseBlock(cond.ifFalse, dep)
      }
      case _ =>
        ()
    })
  }

  private def setRequiresPerms(
    scope: DependencyScope,
    program: ProgramDependenciesImpl,
    collect: mutable.HashSet[String]
  ): Unit = {
    scope.children.foreach(setRequiresPerms(_, program, collect))

    if (!scope.requiresPerms) {
      scope.requiresPerms = deepRequiresPerms(scope, program, collect)
      collect.clear()
    }
  }

  private def setModifiesPerms(
    scope: DependencyScope,
    program: ProgramDependenciesImpl,
    collect: mutable.HashSet[String]
  ): Unit = {
    scope.children.foreach(setModifiesPerms(_, program, collect))

    if (!scope.modifiesPerms) {
      scope.modifiesPerms = deepModifiesPerms(scope, program, collect)
      collect.clear()
    }
  }

  // Given a set of methods already explored, checks whether there are any child
  // scopes or method calls that require a dynamic set of permissions
  private def deepRequiresPerms(
    scope: DependencyScope,
    program: ProgramDependenciesImpl,
    collect: mutable.HashSet[String]
  ): Boolean = {
    // Check the current scope
    scope.requiresPerms ||
    // Recursively check child scopes that inherit permissions
    scope.children.exists(c =>
      c.inheritsPerms &&
      deepRequiresPerms(c, program, collect)) ||
    // Recursively check methods when they have not been visited
    scope.calls.exists(c => program.methods.get(c.callee.name) match {
      case None => false // Ignore external methods
      case Some(m) =>
        m.inheritsPerms &&
        collect.add(m.method.name) &&
        deepRequiresPerms(m, program, collect)
    })
  }

  // Given a set of methods already explored, checks whether there are any child
  // scopes or method calls that can modify a dynamic set of permissions
  private def deepModifiesPerms(
    scope: DependencyScope,
    program: ProgramDependenciesImpl,
    collect: mutable.HashSet[String]): Boolean = {
    // Check the current scope
    // Assume that if the method is precise (`returnsPerms` is false), then
    // `modifiesPerms` has been correctly set, since it can be determined by
    // analyzing the specification without recursing
    scope.modifiesPerms || (scope.returnsPerms && (
      // Recursively check child scopes that return permissions
      scope.children.exists(c =>
        c.returnsPerms &&
        deepModifiesPerms(c, program, collect)) ||
      // Recursively check methods when they have not been visited
      scope.calls.exists(c => program.methods.get(c.callee.name) match {
        case None => false // Ignore external methods
        case Some(m) =>
          collect.add(m.method.name) && deepModifiesPerms(m, program, collect)
      }))
    )
  }

  private def requiresPerms(checks: Seq[RuntimeCheck]): Boolean =
    checks.exists(_.check match {
      case _: AccessibilityCheck => true
      case _ => false
    })

  private def refsPerms(spec: IR.Expression): Boolean = {
    spec match {
      case _: IR.Accessibility | _: IR.PredicateInstance | _: IR.Imprecise => true
      case x: IR.Conditional => refsPerms(x.ifTrue) || refsPerms(x.ifFalse)
      case _ => false
    }
  }

  private def refsPerms(spec: Option[IR.Expression]): Boolean =
    spec match {
      case None => false
      case Some(e) => refsPerms(e)
    }
}
