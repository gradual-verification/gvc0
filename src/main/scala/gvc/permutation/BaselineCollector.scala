package gvc.permutation
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{
  Assert,
  AssertKind,
  Block,
  FieldMember,
  Invoke,
  Method,
  Op,
  Program,
  Return,
  While
}
import gvc.weaver.Collector.hasImplicitReturn

import scala.collection.mutable

object BaselineCollector {

  case class CollectedFraming(op: Op, fields: List[FieldMember])

  case class BaselineCollectedMethod(
      method: Method,
      calls: List[Invoke],
      allocations: List[Op],
      assertions: List[Assert],
      whileLoops: List[While],
      framing: List[CollectedFraming],
      returns: List[Return],
      hasImplicitReturn: Boolean
  )
  def collect(irProgram: Program): Map[String, BaselineCollectedMethod] = {
    irProgram.methods.map(m => (m.name, collect(m))).toMap
  }
  def collect(irMethod: Method): BaselineCollectedMethod = {
    val calls = mutable.ListBuffer[Invoke]()
    val allocations = mutable.ListBuffer[Op]()
    val assertions = mutable.ListBuffer[Assert]()
    val whileLoops = mutable.ListBuffer[While]()
    val framing = mutable.ListBuffer[CollectedFraming]()
    val returns = mutable.ListBuffer[Return]()

    def collectMembers(
        expr: IRGraph.Expression,
        members: mutable.ListBuffer[FieldMember]
    ): Unit = {
      expr match {
        case member: FieldMember => members += member
        case conditional: IRGraph.Conditional =>
          collectMembers(conditional.condition, members)
          collectMembers(conditional.ifTrue, members)
          collectMembers(conditional.ifFalse, members)
        case binary: IRGraph.Binary =>
          collectMembers(binary.right, members)
          collectMembers(binary.left, members)
        case unary: IRGraph.Unary => collectMembers(unary.operand, members)
        case _                    =>
      }
    }

    def collectBlock(block: Block): Unit =
      block.foreach(op => {
        val members = mutable.ListBuffer[FieldMember]()

        op match {
          case invoke: Invoke =>
            calls += invoke
            if (invoke.target.isDefined)
              collectMembers(invoke.target.get, members)
            invoke.arguments.foreach(collectMembers(_, members))

          case value: IRGraph.AllocValue =>
            allocations += value

          case struct: IRGraph.AllocStruct =>
            allocations += struct
            collectMembers(struct.target, members)

          case array: IRGraph.AllocArray =>
            allocations += array

          case assignMember: IRGraph.AssignMember =>
            assignMember.member match {
              case member: FieldMember => members += member
              case _                   =>
            }
            collectMembers(assignMember.value, members)

          case assign: IRGraph.Assign =>
            collectMembers(assign.value, members)

          case assert: Assert =>
            if (assert.kind == AssertKind.Specification)
              assertions += assert
            else
              collectMembers(assert.value, members)

          case returnStmt: IRGraph.Return =>
            returns += returnStmt
            if (returnStmt.value.isDefined)
              collectMembers(returnStmt.value.get, members)

          case value: IRGraph.If =>
            collectMembers(value.condition, members)
            collectBlock(value.ifTrue)
            collectBlock(value.ifFalse)

          case value: IRGraph.While =>
            if (value.invariant.isDefined)
              whileLoops += value
            collectMembers(value.condition, members)
            collectBlock(value.body)

          case _ =>
        }
        if (members.nonEmpty)
          framing += CollectedFraming(op, members.toList)
      })

    collectBlock(irMethod.body)

    val impliedReturn =
      irMethod.body.lastOption match {
        case None         => true
        case Some(tailOp) => hasImplicitReturn(tailOp)
      }

    BaselineCollectedMethod(
      irMethod,
      calls.toList,
      allocations.toList,
      assertions.toList,
      whileLoops.toList,
      framing.toList,
      returns.toList,
      impliedReturn
    )
  }
}
