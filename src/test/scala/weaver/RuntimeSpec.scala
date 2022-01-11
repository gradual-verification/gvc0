package weaver

import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer.{IRGraph, GraphPrinter}
import gvc.weaver.CheckRuntime

class RuntimeSpec extends AnyFunSuite {
  test("add to program") {
    val program = new IRGraph.Program()
    val runtime = CheckRuntime.addToIR(program)

    assert(GraphPrinter.print(program, true).trim() == "#use <runtime>")

    assert(program.method(CheckRuntime.Names.assertAcc) == runtime.assertAcc)
    assert(program.struct(CheckRuntime.Names.ownedFields) == runtime.ownedFields)
  }
}