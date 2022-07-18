package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import gvc.Main.ProfilingInfo
import doobie._
import doobie.implicits._
import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.SpecType.SpecType
import cats.effect.unsafe.implicits.global
import gvc.CC0Wrapper
import gvc.benchmarking.BenchmarkExecutor.ReservedProgram

import scala.collection.mutable

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

object DAO {

  type DBConnection = Transactor.Aux[IO, Unit]

  case class Hardware(id: Long, hardwareName: String, dateAdded: String)

  case class StoredProgram(id: Long,
                           hash: String,
                           dateAdded: String,
                           numLabels: Long)

  case class Version(id: Long, versionName: String, dateAdded: String)

  case class Permutation(id: Long,
                         programID: Long,
                         permutationHash: String,
                         dateAdded: String)

  case class Step(pathID: Long, permutationID: Long, levelID: Long)

  case class Conjuncts(id: Long,
                       permutationID: Long,
                       versionID: Long,
                       total: Long,
                       eliminated: Long,
                       date: String)

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

  private val DB_DRIVER = "com.mysql.cj.jdbc.Driver"

  def connect(credentials: BenchmarkDBCredentials): DBConnection = {
    val connection = Transactor.fromDriverManager[IO](
      DB_DRIVER,
      credentials.url, //"jdbc:mysql://localhost:3306/", // connect URL (driver-specific)
      credentials.username,
      credentials.password
    )
    Output.success(
      s"Connected to database as ${credentials.username}@${credentials.url}")
    connection
  }

  def addOrResolveHardware(name: String,
                           xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    (for {
      _ <- sql"CALL sp_gr_Hardware($name, @hw);".query.unique
      hid <- sql"SELECT @hw;".query[Long].option
    } yield hid)
      .transact(xa)
      .unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(s"Failed to add or resolve hardware $name")
    }
  }

  def addOrResolveVersion(name: String,
                          xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    (for {
      _ <- sql"CALL sp_gr_Version($name, @ver);".query.unique
      vid <- sql"SELECT @ver;".query[Long].option
    } yield vid)
      .transact(xa)
      .unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(s"Failed to add or resolve version $name")
    }
  }

  def addOrResolveProgram(filename: java.nio.file.Path,
                          hash: String,
                          numLabels: Long,
                          xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    val name = filename.getFileName.toString
    (for {
      _ <- sql"CALL sp_gr_Program($name, $hash, $numLabels, @pid);".update.run
      pid <- sql"SELECT @pid;".query[Long].option
    } yield pid)
      .transact(xa)
      .unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(s"Failed to add or resolve program $name")
    }
  }

  case class StoredComponent(id: Long,
                             programID: Long,
                             contextName: String,
                             specType: SpecType,
                             specIndex: Long,
                             exprType: ExprType,
                             exprIndex: Long,
                             dateAdded: String)

  def addOrResolveComponent(programID: Long,
                            astLabel: ASTLabel,
                            xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    val contextName = astLabel.parent match {
      case Left(value)  => value.name
      case Right(value) => value.name
    }
    (for {
      _ <- sql"CALL sp_gr_Component($programID, $contextName, ${astLabel.specType}, ${astLabel.specIndex}, ${astLabel.exprType}, ${astLabel.exprIndex}, @comp);".update.run
      cid <- sql"SELECT @comp;".query[Long].option
    } yield cid).transact(xa).unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(
          s"Failed to add or resolve component ${astLabel.hash}")
    }
  }

  def addOrResolvePermutation(programID: Long,
                              permutationHash: String,
                              xa: DBConnection): Long = {
    (for {
      _ <- sql"""CALL sp_gr_Permutation($programID, $permutationHash, @perm);""".update.run
      pid <- sql"""SELECT @perm;""".query[Long].option
    } yield pid).transact(xa).unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(
          s"Failed to add or resolve permutation $permutationHash")
    }
  }

  def getNumberOfPaths(programID: Long, xa: DBConnection): Int = {
    sql"SELECT COUNT(*) FROM paths WHERE program_id = $programID"
      .query[Int]
      .option
      .transact(xa)
      .unsafeRunSync() match {
      case Some(value) => value
      case None =>
        throw new DBException(
          s"Failed to query for number of paths corresponding to a given program.")
    }
  }

  def addConjuncts(version: Version,
                   hardware: Hardware,
                   permutation: Permutation,
                   profiling: ProfilingInfo,
                   xa: transactor.Transactor.Aux[IO, Unit])
    : ConnectionIO[Option[Conjuncts]] = {
    sql"""
        INSERT INTO conjuncts 
            (permutation_id, version_id, hardware_id, conj_total, conj_eliminated) 
        VALUES (${permutation.id}, ${version.id}, ${hardware.id}, ${profiling.nConjuncts}, ${profiling.nConjunctsEliminated});
    """.query[Conjuncts].option
  }

  def reserveProgram(version: Long,
                     hardware: Long,
                     workloads: List[Int],
                     xa: DBConnection): Option[ReservedProgram] = {
    for (i <- workloads) {
      val reserved = (for {
        _ <- sql"""CALL sp_ReservePermutation($version, $hardware, @perm, @perf);""".update.run
        perf_id <- sql"""SELECT @perf;""".query[Long].option
        perm <- sql"""SELECT * FROM permutations WHERE id = (SELECT @perm);"""
          .query[Permutation]
          .option
      } yield (perf_id, perm)).transact(xa).unsafeRunSync()
      reserved._1 match {
        case Some(perfID) =>
          reserved._2 match {
            case Some(perm) => ReservedProgram(perm, i, perfID)
            case None       =>
          }
        case None =>
      }
    }
    None
  }

  def updatePerformance(perfID: Long,
                        perfData: CC0Wrapper.Performance,
                        conn: DBConnection): Unit = {
    sql"""UPDATE performance SET
         performance_date = DEFAULT,
         mean = ${perfData.mean},
         median = ${perfData.median},
         maximum = ${perfData.maximum},
         minimum = ${perfData.minimum},
         fifth = ${perfData.fifth},
         ninety_fifth = ${perfData.ninetyFifth},
         stdev = ${perfData.stdev}
                   WHERE id = $perfID""".query.unique
      .transact(conn)
      .unsafeRunSync()
  }

  def containsPath(programID: Long,
                   pathHash: String,
                   xa: DBConnection): Boolean = {
    sql"SELECT * FROM paths WHERE program_id = $programID AND path_hash = $pathHash"
      .query[ProgramPath]
      .option
      .transact(xa)
      .unsafeRunSync()
      .nonEmpty
  }

  class PathQueryCollection(hash: String,
                            programID: Long,
                            bottomPermutationID: Long) {

    private case class Step(permID: Long,
                            levelID: Long,
                            componentID: Long,
                            pathID: Long)

    private val steps = mutable.ListBuffer[(Long, Long)]()

    def addStep(perm: Long, componentID: Long): Unit = {
      steps += Tuple2(perm, componentID)
    }

    def exec(xa: DBConnection): Unit = {
      val massUpdate = for {
        _ <- sql"""INSERT INTO paths
             (path_hash, program_id)
         VALUES
             ($hash, $programID);""".update.run
        id <- sql"SELECT LAST_INSERT_ID()".query[Long].unique
        _ <- sql"INSERT INTO steps (permutation_id, level_id, path_id) VALUES ($bottomPermutationID, 0, $id)".update.run
        v <- Update[Step](
          s"INSERT INTO steps (permutation_id, level_id, component_id, path_id) VALUES (?, ?, ?, ?)")
          .updateMany(
            this.steps.indices
              .map(i => Step(this.steps(i)._1, i + 1, this.steps(i)._2, id))
              .toList)
      } yield v
      massUpdate.transact(xa).unsafeRunSync()
    }
  }
}
