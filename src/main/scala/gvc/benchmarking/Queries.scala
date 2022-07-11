package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import gvc.Main.ProfilingInfo

import doobie._
import doobie.implicits._
import gvc.benchmarking.BenchmarkSequential.BenchmarkException
import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.ModeMeasured.ModeMeasured
import gvc.benchmarking.SpecType.SpecType
import cats.effect.unsafe.implicits.global

class DBException(message: String) extends Exception(message)

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

case class Hardware(id: Long, hardwareName: String, dateAdded: String)

case class Version(id: Long, versionName: String, dateAdded: String)

case class Program(id: Long, hash: String, dateAdded: String, numLabels: Long)

case class Permutation(id: Long,
                       programID: Long,
                       pathID: Long,
                       levelID: Long,
                       componentID: Long,
                       dateAdded: String)

case class Step(pathID: Long, permutationID: Long, levelID: Long)

case class Conjuncts(id: Long,
                     permutationID: Long,
                     versionID: Long,
                     total: Long,
                     eliminated: Long,
                     date: String)

case class Component(id: Long,
                     functionName: String,
                     specType: SpecType,
                     exprType: ExprType,
                     specIndex: Long,
                     exprIndex: Long,
                     dateAdded: String)

case class ProgramPath(id: Long, hash: String, programID: Long)

case class StoredPerformance(id: Long,
                             programID: Long,
                             versionID: Long,
                             hardwareID: Long,
                             performanceDate: String,
                             modeMeasured: String,
                             stress: Int,
                             iter: Int,
                             ninetyFifth: BigDecimal,
                             fifth: BigDecimal,
                             median: BigDecimal,
                             mean: BigDecimal,
                             stdev: BigDecimal,
                             minimum: BigDecimal,
                             maximum: BigDecimal)

class Queries {

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

  def getHardware(name: String): Option[Hardware] =
    sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE hardware_name = $name;"
      .query[Hardware]
      .option
      .transact(xa)
      .unsafeRunSync()

  def addHardware(name: String): Option[Hardware] = {
    val constructed = for {
      _ <- sql"INSERT INTO hardware (hardware_name) VALUES ($name);".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      h <- sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE id = $id;"
        .query[Hardware]
        .option
    } yield h
    xa.trans.apply(constructed).unsafeRunSync()
  }

  def getVersion(name: String): ConnectionIO[Option[Version]] =
    sql"SELECT id, version_name, version_date FROM versions WHERE version_name = $name;"
      .query[Version]
      .option

  def addVersion(name: String): ConnectionIO[Option[Version]] = {
    for {
      _ <- sql"INSERT INTO versions (version_name) VALUES ($name);".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      v <- sql"SELECT id, version_name, version_date FROM versions WHERE id = $id;"
        .query[Version]
        .option
    } yield v
  }

  def addOrResolveProgram(filename: java.nio.file.Path,
                          hash: String,
                          numLabels: Long): Program = {
    val addition = for {
      _ <- sql"INSERT INTO programs (src_filename, src_hash, num_labels) VALUES (${filename.getFileName.toString}, $hash, $numLabels)".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      v <- sql"SELECT id FROM programs WHERE id = $id;"
        .query[Program]
        .option
    } yield v
    xa.trans.apply(addition).unsafeRunSync() match {
      case Some(value) => value
      case None =>
        val resolution =
          sql"SELECT id FROM programs WHERE src_filename = ${filename.getFileName.toString} AND src_hash = $hash AND num_labels = $numLabels"
            .query[Program]
            .option
            .transact(xa)
            .unsafeRunSync()
        resolution match {
          case Some(v: Program) => v
          case None =>
            throw new DBException(
              s"Failed to update or resolve program ${filename.toAbsolutePath.toString}")
        }
    }
  }

  def addComponent(program: Program,
                   functionName: String,
                   specType: SpecType,
                   exprType: ExprType,
                   specIndex: Long,
                   exprIndex: Long): ConnectionIO[Option[Component]] = {
    for {
      _ <- sql"""INSERT INTO components
             (program_id, fn_name, spec_type, spec_index, expr_type, expr_index)
         VALUES 
             (${program.id}, $functionName, $specType, $specIndex, $exprType, $exprIndex);""".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      c <- sql"SELECT (program_id, fn_name, spec_type, spec_index, expr_type, expr_index) FROM components WHERE id = $id;"
        .query[Component]
        .option
    } yield c

  }

  def addPermutation(
      program: Program,
      permutationHash: String): ConnectionIO[Option[Permutation]] = {
    for {
      _ <- sql"INSERT INTO permutations (program_id, permutation_hash) VALUES (${program.id}, $permutationHash);".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      c <- sql"SELECT (id, program_id, permutation_hash) FROM permutations WHERE id = $id;"
        .query[Permutation]
        .option
    } yield c
  }

  def addStep(perm: Permutation,
              path: ProgramPath,
              levelID: Long): ConnectionIO[Option[Step]] = {
    for {
      _ <- sql"INSERT INTO steps (perm_id, path_id, level_id) VALUES (${perm.id}, ${path.id}, $levelID);".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      s <- sql"SELECT (id, perm_id, path_id, level_id) FROM steps WHERE id = $id;"
        .query[Step]
        .option
    } yield s
  }

  def addPath(hash: String,
              programID: Long): ConnectionIO[Option[ProgramPath]] = {

    for {
      _ <- sql"INSERT INTO paths (path_hash, program_id) VALUES ($hash, $programID);".update.run
      id <- sql"select LAST_INSERT_ID()".query[Long].unique
      p <- sql"SELECT (id, path_hash, program_id) FROM paths WHERE id = $id;"
        .query[ProgramPath]
        .option
    } yield p
  }

  def addConjuncts(
      version: Version,
      hardware: Hardware,
      permutation: Permutation,
      profiling: ProfilingInfo): ConnectionIO[Option[Conjuncts]] = {
    sql"""
        INSERT INTO conjuncts 
            (perm_id, version_id, hardware_id, conj_total, conj_eliminated) 
        VALUES (${permutation.id}, ${version.id}, ${hardware.id}, ${profiling.nConjuncts}, ${profiling.nConjunctsEliminated});
    """.query[Conjuncts].option
  }

  def addPerformance(pg: Program,
                     version: Version,
                     hardware: Hardware,
                     modeMeasured: ModeMeasured,
                     stress: Option[Int],
                     iter: Int,
                     perf: gvc.CC0Wrapper.Performance)
    : ConnectionIO[Option[StoredPerformance]] = {
    sql"""INSERT INTO performance (
                program_id,
                version_id, 
                hw_id, 
                mode_measured, 
                stress, 
                iter, 
                ninety_fifth, 
                fifth, 
                median, 
                mean, 
                stdev, 
                minimum, 
                maximum
            )
         VALUES (
                 ${pg.id}, 
                 ${version.id}, 
                 ${hardware.id}, 
                 $modeMeasured, 
                 ${stress.getOrElse(0)}, 
                 $iter, 
                 ${perf.ninetyFifth}, 
                 ${perf.fifth}, 
                 ${perf.median}, 
                 ${perf.mean}, 
                 ${perf.stdev}, 
                 ${perf.minimum}, 
                 ${perf.maximum}
                 );
       """.query[StoredPerformance].option
  }
}
