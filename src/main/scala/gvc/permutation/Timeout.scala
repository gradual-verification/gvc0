package gvc.permutation
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.concurrent.duration._
import scala.language.postfixOps

object Timeout {
  def runWithTimeout[T](timeoutMs: Long)(f: => T): Option[T] = {
    Some(Await.result(Future(f), timeoutMs milliseconds))
  }
}
