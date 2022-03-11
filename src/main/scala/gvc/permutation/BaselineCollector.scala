package gvc.permutation
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph.{
  Assert,
  AssertKind,
  Block,
  Invoke,
  Member,
  Method,
  Op,
  Program,
  Return,
  While
}

import scala.collection.mutable

class BaselineCollector {

  case class BaselineCollectedProgram(
      program: Program,
      methods: Map[scala.Predef.String, BaselineCollectedMethod]
  )

  case class CollectedFraming(op: Op, member: List[Member])

  case class BaselineCollectedMethod(
      method: Method,
      calls: List[Invoke],
      allocations: List[Op],
      specAssertions: List[Assert],
      whileInvariants: List[While],
      dereferences: List[CollectedFraming]
  )
  def collect(irProgram: Program): BaselineCollectedProgram = {
    val methods =
      irProgram.methods.map(m => (m.name, collect(irProgram, m))).toMap

    BaselineCollectedProgram(irProgram, methods)
  }
  def collect(irProgram: Program, irMethod: Method): BaselineCollectedMethod = {
    val calls = mutable.ListBuffer[Invoke]()
    val allocations = mutable.ListBuffer[Op]()
    val specAssertions = mutable.ListBuffer[Assert]()
    val whileInvariants = mutable.ListBuffer[While]()
    val dereferences = mutable.ListBuffer[CollectedFraming]()
    val returns = mutable.ListBuffer[Return]()

    def collectMembers(
        expr: IRGraph.Expression,
        members: mutable.ListBuffer[Member]
    ): Unit = {
      expr match {
        case member: Member => members += member
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

    def collectBlock(block: Block): Unit = {
      block.foreach(op => {
        val members = mutable.ListBuffer[Member]()

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
            members += assignMember.member
            collectMembers(assignMember.value, members)

          case assign: IRGraph.Assign =>
            collectMembers(assign.value, members)

          case assert: Assert =>
            if (assert.kind == AssertKind.Specification)
              specAssertions += assert
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
              whileInvariants += value
            collectMembers(value.condition, members)
            collectBlock(value.body)

          case _ =>
        }
        if (members.nonEmpty)
          dereferences += CollectedFraming(op, members.toList)
      })
    }

    collectBlock(irMethod.body)
    BaselineCollectedMethod(
      irMethod,
      calls.toList,
      allocations.toList,
      specAssertions.toList,
      whileInvariants.toList,
      dereferences.toList
    )
  }
}
