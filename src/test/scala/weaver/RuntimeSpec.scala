package weaver

import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer.{IRGraph, GraphPrinter}
import gvc.weaver.CheckRuntime

class RuntimeSpec extends AnyFunSuite {
  test("add to program") {
    val program = new IRGraph.Program()
    val runtime = CheckRuntime.addToIR(program)

    assert(GraphPrinter.print(program, true).trim() == "#use <runtime>")

    assert(runtime.methods.contains(program.method(CheckRuntime.Names.assertAcc)))
    assert(runtime.structs.contains(program.struct(CheckRuntime.Names.ownedFields)))
  }
}