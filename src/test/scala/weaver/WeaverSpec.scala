package gvteal.specs.weaver

import gvteal.specs._
import org.scalatest.funsuite.AnyFunSuite
import gvteal.transformer._
import gvteal.weaver.Weaver

class WeaverSpec extends AnyFunSuite {

  test("resolve empty method") {
    val program = TestUtils.program(
      """
      int main()
      {
        return 0;
      }
      """
    )

    Weaver.weave(program.ir, program.silverProgram)
    val output = IRPrinter.print(program.ir, false)

    assert(
      output ==
        """|#use <runtime>
         |int main();
         |
         |int main()
         |{
         |  int* _instanceCounter = NULL;
         |  _instanceCounter = alloc(int);
         |  return 0;
         |}
         |""".stripMargin
    )
  }
}
