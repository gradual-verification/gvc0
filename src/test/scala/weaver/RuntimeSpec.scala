package weaver

import gvteal.specs.BaseFileSpec
import org.scalatest.funsuite.AnyFunSuite
import gvteal.transformer.{IRPrinter, IR}
import gvteal.weaver.CheckRuntime

class RuntimeSpec extends AnyFunSuite with BaseFileSpec {

  test("add to program") {
    val program = new IR.Program()
    val runtime = CheckRuntime.addToIR(program)

    assert(IRPrinter.print(program, true).trim() == "#use <runtime>")

    assert(program.method(CheckRuntime.Names.assertAcc) == runtime.assertAcc)
    assert(
      program.struct(
        CheckRuntime.Names.ownedFieldsStruct
      ) == runtime.ownedFields
    )
  }
}
