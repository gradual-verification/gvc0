package transformer

import org.scalatest.funsuite._
import gvc.specs.TestUtils

class ArraySilverSpec extends AnyFunSuite {
  test("primitive arrays lower to printable Silver") {
    val program = TestUtils.program("""
      |int main()
      |  //@requires true;
      |  //@ensures true;
      |{
      |  int[] a = alloc_array(int, 3);
      |  a[0] = 1;
      |  return \length(a);
      |}
      |""".stripMargin)

    val vpr = program.silverSource
    assert(vpr.contains("Array[Int]"))
    assert(vpr.contains("Array[Int](3)"))
    assert(vpr.contains("a[0]"))
    assert(vpr.contains("|a|"))
  }
}