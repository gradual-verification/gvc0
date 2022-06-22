package gvc.benchmarking
import doobie._
import doobie.implicits._
import cats.effect.unsafe.implicits.global
import cats.effect.IO
import gvc.benchmarking.Bench.BenchmarkException

//reference doobie tutorial: https://tpolecat.github.io/doobie/docs/03-Connecting.html
class BenchmarkDatabase {
  private val DB_DRIVER = "org.postgresql.Driver"
  private val DB_URL = sys.env.get("GVC0_DB_URL") match {
    case Some(value) => value
    case None =>
      throw new BenchmarkException(
        "Unable to resolve $GVC0_DB_URL from environment."
      )
  }
  private val DB_USER = sys.env.get("GVC0_DB_USER") match {
    case Some(value) => value
    case None =>
      throw new BenchmarkException(
        "Unable to resolve $GVC0_DB_USER from environment."
      )
  }
  private val DB_PASS = sys.env.getOrElse("GVC0_DB_PASS", "")
  private val xa = Transactor.fromDriverManager[IO](
    DB_DRIVER,
    DB_USER,
    DB_URL,
    DB_PASS
  )
}
