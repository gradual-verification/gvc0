import org.scalatest.funsuite._
import gvteal.transformer.IR

class IRSpec extends AnyFunSuite {
  test("get method from body block") {
    val method = new IR.Method("test", None)
    assert(method.body.method == method)
  }

  test("get method from op in if block") {
    val method = new IR.Method("test", None)
    val ifOp = new IR.If(new IR.BoolLit(true))
    val errOp = new IR.Error(new IR.NullLit())
    ifOp.ifTrue += errOp
    method.body += ifOp
    assert(errOp.method == method)
  }

  test("get method from op in while block") {
    val method = new IR.Method("test", None)
    val whileOp = new IR.While(new IR.BoolLit(true), new IR.BoolLit(true))
    val errOp = new IR.Error(new IR.NullLit())
    whileOp.body += errOp
    method.body += whileOp
    assert(errOp.method == method)
  }

  test("add single op") {
    val method = new IR.Method("test", None)
    val errOp = new IR.Error(new IR.NullLit())
    method.body += errOp
    assert(method.body.toList == List(errOp))
  }

  test("add two ops") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    method.body += first
    method.body += second
    assert(method.body.toList == List(first, second))
  }

  test("prepend single op") {
    val method = new IR.Method("test", None)
    val errOp = new IR.Error(new IR.NullLit())
    errOp +=: method.body
    assert(method.body.toList == List(errOp))
  }

  test("prepend two ops") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    first +=: method.body
    second +=: method.body
    assert(method.body.toList == List(second, first))
  }

  test("remove single op") {
    val method = new IR.Method("test", None)
    val errOp = new IR.Error(new IR.NullLit())
    method.body += errOp
    errOp.remove()
    assert(method.body.isEmpty)
  }

  test("remove first op") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    method.body += first
    method.body += second
    first.remove()
    assert(method.body.toList == List(second))
  }

  test("remove second op") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    method.body += first
    method.body += second
    second.remove()
    assert(method.body.toList == List(first))
  }

  test("insertBefore single op") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    method.body += first
    first.insertBefore(second)
    assert(method.body.toList == List(second, first))
  }

  test("insertBefore multiple") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.IntLit(1))
    val third = new IR.Error(new IR.IntLit(2))
    method.body += first
    first.insertBefore(Seq(second, third))
    assert(method.body.toList == List(second, third, first))
  }

  test("insertAfter single op") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    method.body += first
    first.insertAfter(second)
    assert(method.body.toList == List(first, second))
  }

  test("insertAfter multiple") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.IntLit(1))
    val third = new IR.Error(new IR.IntLit(2))
    method.body += first
    first.insertAfter(Seq(second, third))
    assert(method.body.toList == List(first, second, third))
  }

  test("insertBefore into middle") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    val middle = new IR.Error(new IR.IntLit(1))
    method.body += first
    method.body += second
    second.insertBefore(middle)
    assert(method.body.toList == List(first, middle, second))
  }

  test("insertAfter into middle") {
    val method = new IR.Method("test", None)
    val first = new IR.Return(None)
    val second = new IR.Error(new IR.NullLit())
    val middle = new IR.Error(new IR.IntLit(1))
    method.body += first
    method.body += second
    first.insertAfter(middle)
    assert(method.body.toList == List(first, middle, second))
  }

  test("combine all inserts and remove") {
    val method = new IR.Method("test", None)
    val one = new IR.Error(new IR.IntLit(1))
    val two = new IR.Error(new IR.IntLit(2))
    val three = new IR.Error(new IR.IntLit(3))
    val four = new IR.Error(new IR.IntLit(4))
    method.body += four
    one +=: method.body

    four.insertBefore(three)
    one.insertAfter(two)
    four.remove()
    one.remove()
    two.insertBefore(one)
    three.insertAfter(four)

    assert(method.body.toList == List(one, two, three, four))
  }
}
