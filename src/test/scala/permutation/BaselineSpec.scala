package gvc.specs.permutation

import org.scalatest.funsuite.AnyFunSuite

import gvc.specs._
import gvc.specs.BaseFileSpec
import gvc.transformer.GraphPrinter
import gvc.permutation.BaselineChecker

class BaselineSpec extends AnyFunSuite with BaseFileSpec {
  for (input <- TestUtils.groupResources("baseline")) {
    test("test " + input.name) {
      val ir = TestUtils.program(input(".c0").read()).ir

      BaselineChecker.check(ir)
      val output = GraphPrinter.print(ir, false)
      assertFile(input(".baseline.c0"), output)
    }
  }
}
