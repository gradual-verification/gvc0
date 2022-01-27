package weaver

import gvc.specs.BaseFileSpec
import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer.{GraphPrinter, IRGraph}
import gvc.weaver.CheckRuntime

class RuntimeSpec extends AnyFunSuite with BaseFileSpec {

  test("add to program") {
    val program = new IRGraph.Program()
    val runtime = CheckRuntime.addToIR(program)

    assert(GraphPrinter.print(program, true).trim() == "#use <runtime>")

    assert(program.method(CheckRuntime.Names.assertAcc) == runtime.assertAcc)
    assert(
      program.struct(
        CheckRuntime.Names.ownedFieldsStruct
      ) == runtime.ownedFields
    )
  }
}
