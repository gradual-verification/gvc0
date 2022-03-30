package gvc.specs.weaver

import gvc.specs._
import org.scalatest.funsuite.AnyFunSuite
import gvc.transformer._
import gvc.weaver.Weaver

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
    val output = GraphPrinter.print(program.ir, false)

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
