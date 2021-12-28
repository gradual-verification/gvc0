import org.scalatest.funsuite._
import gvc.transformer.IRGraph._

class IRGraphSpec extends AnyFunSuite {
  test("get method from body block") {
    val method = new Method("test", None)
    assert(method.body.method == method)
  }

  test("get method from op in if block") {
    val method = new Method("test", None)
    val ifOp = new If(new Bool(true))
    val errOp = new Error(new Null())
    ifOp.ifTrue += errOp
    method.body += ifOp
    assert(errOp.method == method)
  }

  test("get method from op in while block") {
    val method = new Method("test", None)
    val whileOp = new While(new Bool(true), None)
    val errOp = new Error(new Null())
    whileOp.body += errOp
    method.body += whileOp
    assert(errOp.method == method)
  }

  test("add single op") {
    val method = new Method("test", None)
    val errOp = new Error(new Null())
    method.body += errOp
    assert(method.body.toList == List(errOp))
  }

  test("add two ops") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    method.body += first
    method.body += second
    assert(method.body.toList == List(first, second))
  }

  test("remove single op") {
    val method = new Method("test", None)
    val errOp = new Error(new Null())
    method.body += errOp
    errOp.remove()
    assert(method.body.isEmpty)
  }

  test("remove first op") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    method.body += first
    method.body += second
    first.remove()
    assert(method.body.toList == List(second))
  }

  test("remove second op") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    method.body += first
    method.body += second
    second.remove()
    assert(method.body.toList == List(first))
  }

  test("insertBefore single op") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    method.body += first
    first.insertBefore(second)
    assert(method.body.toList == List(second, first))
  }

  test("insertAfter single op") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    method.body += first
    first.insertAfter(second)
    assert(method.body.toList == List(first, second))
  }

  test("insertBefore into middle") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    val middle = new Error(new Int(1))
    method.body += first
    method.body += second
    second.insertBefore(middle)
    assert(method.body.toList == List(first, middle, second))
  }

  test("insertAfter into middle") {
    val method = new Method("test", None)
    val first = new Return(None)
    val second = new Error(new Null())
    val middle = new Error(new Int(1))
    method.body += first
    method.body += second
    first.insertAfter(middle)
    assert(method.body.toList == List(first, middle, second))
  }

  test("combine all inserts and remove") {
    val method = new Method("test", None)
    val one = new Error(new Int(1))
    val two = new Error(new Int(2))
    val three = new Error(new Int(3))
    val four = new Error(new Int(4))
    method.body += one
    method.body += four

    four.insertBefore(three)
    one.insertAfter(two)
    four.remove()
    one.remove()
    two.insertBefore(one)
    three.insertAfter(four)

    assert(method.body.toList == List(one, two, three, four))
  }
}
