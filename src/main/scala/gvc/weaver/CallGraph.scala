package gvc.weaver

import gvc.weaver.Collector.CollectedProgram
import scala.collection.mutable
import gvc.transformer.IR
import gvc.weaver.Collector.CollectedScope
import gvc.weaver.Collector.RuntimeCheck

// This helper class handles calculation of the permission requirements for a
// method; namely, whether a method requires permissions to be passed to it, and
// whether a method may produce permissions. This enables optimization in cases
// when calling an imprecise method that does not have acc runtime checks.

sealed trait PermissionMode

// A method that does not modify permissions.
// Note: this includes completely precise methods, which need permissions
// calculated by the invariant when the caller is tracking permissions
case object NoPermissions extends PermissionMode

// A method that requires a set of permissions to be passed.
case object RequiresPermissions extends PermissionMode

// A method that optionally accepts a set of permissions.
// In other words, the caller *must* pass the set of permissions if it is
// tracking them, but it may pass NULL instead if the caller is not tracking
// permissions
case object OptionalPermissions extends PermissionMode

trait MethodData {
  def requiresPerms: Boolean
  def modifiesPerms: Boolean
  def precisePre: Boolean
  def precisePost: Boolean

  def permissionMode: PermissionMode =
    if (requiresPerms) RequiresPermissions
    else if (modifiesPerms) OptionalPermissions
    else NoPermissions
}

object CallGraph {
  private class CallGraphMethod(
    val precisePre: Boolean,
    val precisePost: Boolean,
    var modifiesPerms: Boolean,
    var requiresPerms: Boolean) extends MethodData {
    val dependencies = mutable.HashSet[String]()
  }
}

class CallGraph(collected: CollectedProgram) {
  private val program = collected.program
  private val predicatePrecision = mutable.HashMap[String, Boolean]()

  def isCompletelyPrecise(pred: IR.Predicate): Boolean = {
    predicatePrecision.get(pred.name) match {
      case Some(v) => v
      case None => {
        predicatePrecision.update(pred.name, true)
        val result = isCompletelyPrecise(pred.expression)
        predicatePrecision.update(pred.name, result)
        result
      }
    }
  }

  def isCompletelyPrecise(e: IR.Expression): Boolean = e match {
    case _: IR.Imprecise => false
    case c: IR.Conditional => isCompletelyPrecise(c.ifTrue) && isCompletelyPrecise(c.ifFalse)
    case p: IR.PredicateInstance => isCompletelyPrecise(p.predicate)
    case _ => true
  }

  def isCompletelyPrecise(e: Option[IR.Expression]): Boolean = e match {
    case None => true
    case Some(e) => isCompletelyPrecise(e)
  }

  private val graph = mutable.HashMap[String, CallGraph.CallGraphMethod]()

  private def transitiveClosure(key: String, collect: mutable.HashSet[String]): Unit = {
    for (v <- graph(key).dependencies) {
      if (collect.add(v)) transitiveClosure(v, collect)
    }
  }

  // Shallowly calculate the requirements and dependencies for each method
  for (c <- collected.methods.values) {
    val m = c.method

    val precisePre = isCompletelyPrecise(m.precondition)
    val precisePost = isCompletelyPrecise(m.postcondition)
    val cgm = new CallGraph.CallGraphMethod(
      precisePre = precisePre,
      precisePost = precisePost,
      modifiesPerms = modifiesPerms(m.body),
      requiresPerms = !(precisePre && precisePost) && checksPerms(c))

    addImpreciseCallees(m, cgm.dependencies)
  }
  
  // Depth-first traversal to find the transitive closure of the dependencies
  for ((k, cgm) <- graph) {
    transitiveClosure(k, cgm.dependencies)

    // If an imprecise method calls a method that checks [or modifies]
    // permissions, everything that modifies it must track [or optionally track]
    // a permission set
    if (!(cgm.precisePre && cgm.precisePost)) {
      cgm.requiresPerms = cgm.requiresPerms ||
        cgm.dependencies.exists(d => graph(d).requiresPerms)

      cgm.modifiesPerms = cgm.modifiesPerms ||
        cgm.dependencies.exists(d => graph(d).modifiesPerms)
    }
  }

  private def addImpreciseCallees(method: IR.Method, callees: mutable.HashSet[String]): Unit = {
    def visit(block: IR.Block): Unit = {
      for (op <- block) {
        op match {
          case x: IR.Invoke if !isCompletelyPrecise(x.method.postcondition) =>
            callees += op.method.name
          case x: IR.If =>
            visit(x.ifTrue); visit(x.ifFalse)
          case x: IR.While if !isCompletelyPrecise(x.invariant) =>
            // Enter a while loop iff the invariant is not precise
            // Precise invariants do not count since any necessary permissions
            // will be calculated inside the loop body
            visit(x.body)
          case _ =>
            ()
        }
      }
    }

    visit(method.body)
  }

  // Checks if executing this block could possibly modify the set of permissions
  private def modifiesPerms(block: IR.Block): Boolean = {
    block.exists(_ match {
      case _: IR.AllocStruct | _: IR.AllocValue | _: IR.AllocArray => true
      case x: IR.If => modifiesPerms(x.ifTrue) || modifiesPerms(x.ifFalse)
      case x: IR.While =>
        if (isCompletelyPrecise(x.invariant)) {
          // If while is completely precise, it will only change permissions if
          // the invariant references some heap location
          refsPerms(x.invariant)
        } else {
          // If while is not completely precise, permissions flow through
          // the loop body, so it modfies perms iff the body does
          modifiesPerms(x.body)
        }
      case _ => false
    })
  }

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

  private def checksPerms(scope: CollectedScope): Boolean = {
    scope.checks.exists(_ match {
      case RuntimeCheck(_, _: AccessibilityCheck, _) => true
      case _ => false
    })
  }

  def apply(methodName: String): MethodData = graph(methodName)
}