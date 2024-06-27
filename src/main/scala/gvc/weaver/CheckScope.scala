package gvc.weaver

import scala.collection.mutable
import gvc.transformer.IR

sealed trait CheckScope {
  def block: IR.Block
  def children: Seq[WhileScope]
  def checks: Seq[RuntimeCheck]
}

sealed trait MethodScope extends CheckScope {
  def method: IR.Method
  def block: IR.Block = method.body
  def conditions: Seq[TrackedCondition]
}

sealed trait WhileScope extends CheckScope {
  def op: IR.While
  def block: IR.Block = op.body
}

class ProgramScope(
  val program: IR.Program,
  val methods: Map[String, MethodScope]
)

object CheckScope {
  private sealed abstract class CheckScopeImplementation extends CheckScope {
    val children = mutable.ListBuffer[WhileScope]()
    val checks = mutable.ArrayBuffer[RuntimeCheck]()
  }

  private sealed class MethodScopeImplementation(
    val method: IR.Method,
    val conditions: Seq[TrackedCondition]
  ) extends CheckScopeImplementation with MethodScope
  private sealed class WhileScopeImplementation(val op: IR.While)
    extends CheckScopeImplementation with WhileScope

  def scope(collected: Collector.CollectedProgram): ProgramScope =
    new ProgramScope(
      collected.program,
      collected.methods.mapValues(cm =>
        scope(cm.checks, cm.conditions, cm.method))
    )

  def scope(
    checks: Seq[RuntimeCheck],
    conditions: Seq[TrackedCondition],
    method: IR.Method
  ): MethodScope = {
    val outer = new MethodScopeImplementation(method, conditions)
    val inner = mutable.HashMap[IR.While, WhileScopeImplementation]()

    def getScope(op: IR.Op): CheckScopeImplementation = {
      if (op.block == method.body) {
        outer
      } else {
        op.block match {
          case c: IR.ChildBlock => c.op match {
            case cond: IR.If => getScope(cond)
            case loop: IR.While =>
              inner.getOrElse(loop, {
                val scope = new WhileScopeImplementation(loop)
                getScope(loop).children += scope
                scope
              })
            case _ => throw new WeaverException("Invalid IR structure")
          }

          case _ => throw new WeaverException("Invalid IR structure")
        }
      }
    }

    for (c <- checks) {
      val scope = c.location match {
        case at: AtOp => getScope(at.op)
        case MethodPre | MethodPost => outer
      }

      scope.checks += c
    }

    outer
  }
}