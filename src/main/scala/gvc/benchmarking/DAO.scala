package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import gvc.benchmarking.Bench.BenchmarkException

object ModeMeasured {
  type ModeMeasured = String
  val Translation = "translation"
  val Verification = "verification"
  val Instrumentation = "instrumentation"
  val Compilation = "compilation"
  val ExecutionGradual = "exec_gradual"
  val ExecutionFraming = "exec_framing"
  val ExecutionDynamic = "exec_dynamic"
}

object Queries {
  case class Hardware(id: Long, hardwareName: String, dateAdded: String)

  def getHardware(name: String): ConnectionIO[Option[Hardware]] =
    sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE hardware_name = $name"
      .query[Hardware]
      .option

  def addHardware(name: String): ConnectionIO[Option[Hardware]] =
    sql"INSERT INTO hardware (hardware_name) VALUES ($name)"
      .query[Hardware]
      .option

  case class Version(id: Long, versionName: String, dateAdded: String)

  def getVersion(name: String): ConnectionIO[Option[Version]] =
    sql"SELECT id, version_name, version_date FROM versions WHERE version_name = $name"
      .query[Version]
      .option

  def addVersion(name: String): ConnectionIO[Option[Version]] =
    sql"INSERT INTO versions (version_name) VALUES ($name)"
      .query[Version]
      .option

  case class Program(id: Long, hash: String, dateAdded: String)

  def getProgram(hash: String): ConnectionIO[Option[Program]] =
    sql"SELECT id, program_hash, program_date FROM programs WHERE program_hash = $hash"
      .query[Program]
      .option

  def addProgram(hash: String): ConnectionIO[Option[Program]] =
    sql"INSERT INTO programs (program_hash) VALUES ($hash)"
      .query[Program]
      .option
}

object MySQLConnection {

  private val DB_DRIVER = "com.mysql.cj.jdbc.Driver"

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

  private val DB_PASS = sys.env.get("GVC0_DB_PASS") match {
    case Some(value) => value
    case None =>
      throw new BenchmarkException(
        "Unable to resolve $GVC0_DB_PASS from environment."
      )
  }

  val xa: transactor.Transactor.Aux[IO, Unit] =
    Transactor.fromDriverManager[IO](
      DB_DRIVER, // driver classname
      DB_URL, //"jdbc:mysql://localhost:3306/", // connect URL (driver-specific)
      DB_USER, // user
      DB_PASS // password
    )
}
