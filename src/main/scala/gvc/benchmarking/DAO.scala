package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import gvc.benchmarking.Bench.BenchmarkException
import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.Queries.Program
import gvc.benchmarking.SpecType.SpecType

import java.nio.file.Path

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

object DAO {
  /*def syncExamplePrograms(hashes: Map[Path, String]): Map[Path, Program] = {
    hashes.foreach(hash => {})
  }*/
  //def syncLabels(program: Program, labels: List[ASTLabel]): Map[ASTLabel, Long]
  //def syncHardware(): Hardware
  //def syncVerifierVersion(): Version

}

object Queries {
  case class Hardware(id: Long, hardwareName: String, dateAdded: String)

  def getHardware(name: String): ConnectionIO[Option[Hardware]] =
    sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE hardware_name = $name;"
      .query[Hardware]
      .option

  def addHardware(name: String): ConnectionIO[Option[Hardware]] =
    sql"INSERT INTO hardware (hardware_name) VALUES ($name);"
      .query[Hardware]
      .option

  case class Version(id: Long, versionName: String, dateAdded: String)

  def getVersion(name: String): ConnectionIO[Option[Version]] =
    sql"SELECT id, version_name, version_date FROM versions WHERE version_name = $name;"
      .query[Version]
      .option

  def addVersion(name: String): ConnectionIO[Option[Version]] =
    sql"INSERT INTO versions (version_name) VALUES ($name);"
      .query[Version]
      .option

  case class Program(id: Long, hash: String, dateAdded: String)

  def getProgram(hash: String): ConnectionIO[Option[Program]] =
    sql"SELECT id, program_hash, program_date FROM programs WHERE program_hash = $hash;"
      .query[Program]
      .option

  def addProgram(hash: String): ConnectionIO[Option[Program]] =
    sql"INSERT INTO programs (program_hash) VALUES ($hash)"
      .query[Program]
      .option

  case class Component(id: Long,
                       functionName: String,
                       specType: SpecType,
                       exprType: ExprType,
                       specIndex: Long,
                       exprIndex: Long,
                       dateAdded: String)

  def addComponent(programID: Long,
                   functionName: String,
                   specType: SpecType,
                   exprType: ExprType,
                   specIndex: Long,
                   exprIndex: Long): ConnectionIO[Option[Component]] =
    sql"""INSERT INTO components 
             (spec_id, fn_name, spec_type, spec_index, expr_type, expr_index) 
         VALUES 
             ($programID, $functionName, $specType, $specIndex, $exprType, $exprIndex);"""
      .query[Component]
      .option

  case class Permutation(id: Long,
                         programID: Long,
                         pathID: Long,
                         levelID: Long,
                         componentID: Long,
                         dateAdded: String)

  def addPermutation(programID: Long,
                     pathID: Long,
                     levelID: Long,
                     componentID: Long): ConnectionIO[Option[Permutation]] =
    sql"INSERT INTO permutations (program_id, path_id, level_id, component_id) VALUES ($programID, $pathID, $levelID, $componentID);"
      .query[Permutation]
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
