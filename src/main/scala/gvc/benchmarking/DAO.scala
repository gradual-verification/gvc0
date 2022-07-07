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

  def addProgram(filename: java.nio.file.Path,
                 hash: String): ConnectionIO[Option[Program]] = {
    sql"INSERT INTO programs (src_filename, src_hash) VALUES (${filename.getFileName.toString}, $hash)"
      .query[Program]
      .option
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
                   exprIndex: Long): ConnectionIO[Option[Component]] =
    sql"""INSERT INTO components 
             (program_id, fn_name, spec_type, spec_index, expr_type, expr_index)
         VALUES 
             (${program.id}, $functionName, $specType, $specIndex, $exprType, $exprIndex);"""
      .query[Component]
      .option

  case class Permutation(id: Long,
                         programID: Long,
                         pathID: Long,
                         levelID: Long,
                         componentID: Long,
                         dateAdded: String)

  def addPermutation(
      program: Program,
      permutationHash: String): ConnectionIO[Option[Permutation]] =
    sql"INSERT INTO permutations (program_id, permutation_hash) VALUES (${program.id}, $permutationHash);"
      .query[Permutation]
      .option

  case class Step(pathID: Long, permutationID: Long, levelID: Long)

  def addStep(perm: Permutation,
              path: Path,
              levelID: Long): ConnectionIO[Option[Permutation]] =
    sql"INSERT INTO steps (perm_id, path_id, level_id) VALUES (${perm.id}, ${path.id}, $levelID);"
      .query[Permutation]
      .option

  case class Path(id: Long, hash: String, programID: Long)

  def addPath(hash: String,
              programID: Long): ConnectionIO[Option[Permutation]] =
    sql"INSERT INTO paths (path_hash, program_id) VALUES ($hash, $programID);"
      .query[Permutation]
      .option

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
    sql"""INSERT INTO conjuncts 
            (perm_id, version_id, hardware_id, conj_total, conj_eliminated) 
        VALUES (${permutation.id}, ${version.id}, ${hardware.id}, ${profiling.nConjuncts}, ${profiling.nConjunctsEliminated});"""
      .query[Conjuncts]
      .option
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
