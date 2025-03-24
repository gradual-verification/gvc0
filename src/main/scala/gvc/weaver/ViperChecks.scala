package gvc.weaver

import scala.collection.mutable
import viper.silicon.state.{CheckPosition, LoopPosition, BranchCond}
import viper.silver.{ast => vpr}

case class ViperCheck(
    check: vpr.Exp,
    conditions: List[ViperBranch],
    location: ViperLocation,
    context: vpr.Exp
)

sealed trait ViperLocation
object ViperLocation {
  case object Value extends ViperLocation
  case object PreInvoke extends ViperLocation
  case object PostInvoke extends ViperLocation
  case object PreLoop extends ViperLocation
  case object PostLoop extends ViperLocation
  case object Fold extends ViperLocation
  case object Unfold extends ViperLocation
  case object Unfolding extends ViperLocation
  case object InvariantLoopStart extends ViperLocation
  case object InvariantLoopEnd extends ViperLocation

  def loop(loopPosition: LoopPosition): ViperLocation = loopPosition match {
    case LoopPosition.After     => ViperLocation.PostLoop
    case LoopPosition.Before    => ViperLocation.PreLoop
    case LoopPosition.Beginning => ViperLocation.InvariantLoopStart
    case LoopPosition.End       => ViperLocation.InvariantLoopEnd
  }

  def forIR(irLocation: Location, vprLocation: ViperLocation): Location =
    irLocation match {
      case at: AtOp =>
        vprLocation match {
          case ViperLocation.PreInvoke | ViperLocation.PreLoop |
              ViperLocation.Fold | ViperLocation.Unfold | ViperLocation.Unfolding |
              ViperLocation.Value =>
            Pre(at.op)
          case ViperLocation.PostInvoke | ViperLocation.PostLoop =>
            Post(at.op)
          case ViperLocation.InvariantLoopStart => LoopStart(at.op)
          case ViperLocation.InvariantLoopEnd   => LoopEnd(at.op)
        }
      case p => {
        if (vprLocation != ViperLocation.Value && vprLocation != ViperLocation.Unfolding)
          throw new WeaverException(s"Invalid location '$vprLocation' '$p'")
        irLocation
      }
    }
}

case class ViperBranch(
    at: vpr.Node,
    location: ViperLocation,
    condition: vpr.Exp
)

object ViperBranch {
  def apply(
      branch: BranchCond,
      program: vpr.Program
  ) = branch match {
    case BranchCond(
        condition,
        position,
        Some(CheckPosition.GenericNode(invoke: vpr.MethodCall))
        ) => {
      // This must be a method pre-condition or post-condition
      val callee = program.findMethod(invoke.methodName)

      val location: ViperLocation =
        if (ViperChecks.isContained(position, callee.posts))
          ViperLocation.PostInvoke
        else if (ViperChecks.isContained(position, callee.pres))
          ViperLocation.PreInvoke
        else
          ViperLocation.Value
      new ViperBranch(invoke, location, condition)
    }

    case BranchCond(
        condition,
        position,
        Some(CheckPosition.GenericNode(unfold: vpr.Unfold))
        ) =>
      new ViperBranch(unfold, ViperLocation.Fold, condition)
    
    case BranchCond(
        condition,
        position,
        Some(CheckPosition.GenericNode(unfolding: vpr.Unfolding))
        ) =>
      new ViperBranch(unfolding, ViperLocation.Unfolding, condition)
      
    case BranchCond(
        condition,
        position,
        Some(CheckPosition.GenericNode(unfold: vpr.Fold))
        ) =>
      new ViperBranch(unfold, ViperLocation.Unfold, condition)

    case BranchCond(
        condition,
        _,
        Some(CheckPosition.Loop(inv, position))
        ) => {
      // This must be an invariant
      if (inv.isEmpty || !inv.tail.isEmpty)
        throw new WeaverException("Invalid loop invariant")

      new ViperBranch(inv.head, ViperLocation.loop(position), condition)
    }

    case BranchCond(condition, position, None) => {
      new ViperBranch(position, ViperLocation.Value, condition)
    }

    case _ => throw new WeaverException("Invalid branch condition")
  }
}

object ViperChecks {
  type CheckMap =
    mutable.HashMap[Int, mutable.ListBuffer[ViperCheck]]

  // Convert the verifier's check map into a ViperCheckMap
  def collect(vprProgram: vpr.Program): CheckMap = {
    val vprChecks = viper.silicon.state.runtimeChecks.getChecks
    val collected = new CheckMap()

    for ((pos, checks) <- vprChecks) {
      val (node, location) = pos match {
        case CheckPosition.GenericNode(node) => (node, ViperLocation.Value)
        case CheckPosition.Loop(invariants, position) => {
          if (invariants.tail.nonEmpty)
            throw new WeaverException("Invalid loop invariant")
          (invariants.head, ViperLocation.loop(position))
        }
      }

      val list =
        collected.getOrElseUpdate(node.uniqueIdentifier, mutable.ListBuffer())
      for (c <- checks) {
        val conditions = c.branchInfo.map(ViperBranch(_, vprProgram)).toList
        list += ViperCheck(c.checks, conditions, location, c.context)
      }
    }

    collected
  }

  def isContained(node: vpr.Node, container: vpr.Node): Boolean = {
    container.visit {
      case n => {
        if (n.uniqueIdentifier == node.uniqueIdentifier) {
          return true
        }
      }
    }

    false
  }

  def isContained(node: vpr.Node, containers: Seq[vpr.Node]): Boolean =
    containers.exists(isContained(node, _))
}
