package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import gvc.Main.ProfilingInfo
import gvc.benchmarking.Bench.BenchmarkException
import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.ModeMeasured.ModeMeasured
import gvc.benchmarking.SpecType.SpecType

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
  //def syncLabels(program: Program, labels: List[ASTLabel]): Map[ASTLabel, Long]
  //def syncHardware(): Hardware
  //def syncVerifierVersion(): Version
}

/*
def insert2(name: String, age: Option[Short]): ConnectionIO[Person] =
  for {
    _  <- sql"insert into person (name, age) values ($name, $age)".update.run
    id <- sql"select lastval()".query[Long].unique
    p  <- sql"select id, name, age from person where id = $id".query[Person].unique
  } yield p
 */

object Queries {
  case class Hardware(id: Long, hardwareName: String, dateAdded: String)

  def getHardware(name: String): ConnectionIO[Option[Hardware]] =
    sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE hardware_name = $name;"
      .query[Hardware]
      .option

  def addHardware(name: String): ConnectionIO[Option[Hardware]] = {
    for {
      _ <- sql"INSERT INTO hardware (hardware_name) VALUES ($name);".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      h <- sql"SELECT id, hardware_name, hardware_date FROM hardware WHERE id = $id;"
        .query[Hardware]
        .option
    } yield h
  }

  case class Version(id: Long, versionName: String, dateAdded: String)

  def getVersion(name: String): ConnectionIO[Option[Version]] =
    sql"SELECT id, version_name, version_date FROM versions WHERE version_name = $name;"
      .query[Version]
      .option

  def addVersion(name: String): ConnectionIO[Option[Version]] = {
    for {
      _ <- sql"INSERT INTO versions (version_name) VALUES ($name);".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      v <- sql"SELECT id, version_name, version_date FROM versions WHERE id = $id;"
        .query[Version]
        .option
    } yield v
  }

  case class Program(id: Long, hash: String, dateAdded: String)

  def addProgram(filename: java.nio.file.Path,
                 hash: String): ConnectionIO[Option[Program]] = {
    for {
      _ <- sql"INSERT INTO programs (src_filename, src_hash) VALUES (${filename.getFileName.toString}, $hash)".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      v <- sql"SELECT id, src_filename, src_hash FROM programs WHERE id = $id;"
        .query[Program]
        .option
    } yield v
  }

  case class Component(id: Long,
                       functionName: String,
                       specType: SpecType,
                       exprType: ExprType,
                       specIndex: Long,
                       exprIndex: Long,
                       dateAdded: String)

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
      id <- sql"select LASTVAL()".query[Long].unique
      c <- sql"SELECT (program_id, fn_name, spec_type, spec_index, expr_type, expr_index) FROM components WHERE id = $id;"
        .query[Component]
        .option
    } yield c
  }

  case class Permutation(id: Long,
                         programID: Long,
                         pathID: Long,
                         levelID: Long,
                         componentID: Long,
                         dateAdded: String)

  def addPermutation(
      program: Program,
      permutationHash: String): ConnectionIO[Option[Permutation]] = {
    for {
      _ <- sql"INSERT INTO permutations (program_id, permutation_hash) VALUES (${program.id}, $permutationHash);".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      c <- sql"SELECT (id, program_id, permutation_hash) FROM permutations WHERE id = $id;"
        .query[Permutation]
        .option
    } yield c
  }

  case class Step(pathID: Long, permutationID: Long, levelID: Long)

  def addStep(perm: Permutation,
              path: Path,
              levelID: Long): ConnectionIO[Option[Step]] = {
    for {
      _ <- sql"INSERT INTO steps (perm_id, path_id, level_id) VALUES (${perm.id}, ${path.id}, $levelID);".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      s <- sql"SELECT (id, perm_id, path_id, level_id) FROM steps WHERE id = $id;"
        .query[Step]
        .option
    } yield s
  }

  case class Path(id: Long, hash: String, programID: Long)

  def addPath(hash: String, programID: Long): ConnectionIO[Option[Path]] = {

    for {
      _ <- sql"INSERT INTO paths (path_hash, program_id) VALUES ($hash, $programID);".update.run
      id <- sql"select LASTVAL()".query[Long].unique
      p <- sql"SELECT (id, path_hash, program_id) FROM paths WHERE id = $id;"
        .query[Path]
        .option
    } yield p
  }

  case class Conjuncts(id: Long,
                       permutationID: Long,
                       versionID: Long,
                       total: Long,
                       eliminated: Long,
                       date: String)

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

  case class Performance(id: Long,
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

  def addPerformance(
      pg: Program,
      version: Version,
      hardware: Hardware,
      modeMeasured: ModeMeasured,
      stress: Option[Int],
      iter: Int,
      perf: gvc.CC0Wrapper.Performance): ConnectionIO[Option[Performance]] = {
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
       """.query[Performance].option
  }

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
