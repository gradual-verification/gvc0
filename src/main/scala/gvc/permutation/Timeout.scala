package gvc.permutation
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.concurrent.duration._
import scala.language.postfixOps

object Timeout {
  def runWithTimeout[T](timeoutMs: Long)(f: => T): Option[T] = {
    Some(Await.result(Future(f), timeoutMs milliseconds))
  }

  def formatMilliseconds(ms: Long): String = {
    if (ms > 1000 * 60 * 60) {
      s"${(ms / (1000 * 60 * 60))} hr"
    } else if (ms > 1000 * 60) {
      s"${(ms / (1000 * 60))} min"
    } else if (ms > 1000) {
      s"${ms / 1000} sec"
    } else {
      s"$ms ms"
    }
  }
}
