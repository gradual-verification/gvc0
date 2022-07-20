package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie.util.transactor
import doobie._
import doobie.implicits._
import gvc.benchmarking.ExprType.ExprType
import gvc.benchmarking.SpecType.SpecType
import cats.effect.unsafe.implicits.global
import gvc.CC0Wrapper.Performance
import gvc.benchmarking.BenchmarkExecutor.ReservedProgram
import gvc.benchmarking.DAO.ErrorType.ErrorType
import gvc.benchmarking.Timing.TimedVerification

import scala.collection.mutable

class DBException(message: String) extends Exception(message)

object DAO {

  type DBConnection = Transactor.Aux[IO, Unit]

  object DynamicMeasurementMode {
    type DynamicMeasurementMode = String
    val Gradual = "gradual"
    val Framing = "framing"
    val Dynamic = "dynamic"
  }

  object ErrorType {
    type ErrorType = String
    val Compilation = "compilation"
    val Execution = "execution"
    val Verification = "verification"
    val Timeout = "timeout"
  }

  case class Hardware(id: Long, hardwareName: String, dateAdded: String)

  case class StoredProgram(id: Long,
                           hash: String,
                           dateAdded: String,
                           numLabels: Long)

  case class GlobalConfiguration(timeoutMinutes: Long, maxPaths: Long)

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

  def resolveGlobalConfiguration(conn: DBConnection): GlobalConfiguration = {
    (sql"SELECT timeout_minutes, max_paths FROM global_configuration LIMIT 1"
      .query[GlobalConfiguration]
      .option
      .transact(conn)
      .unsafeRunSync()) match {
      case Some(value) => value
      case None =>
        throw new DBException(
          "Unable to resolve global database configuration.")
    }
  }

  def addOrResolveHardware(name: String,
                           xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    (for {
      _ <- sql"CALL sp_gr_Hardware($name, @hw);".update.run
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
      _ <- sql"CALL sp_gr_Version($name, @ver);".update.run
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

  def updateStaticProfiling(vid: Long,
                            hid: Long,
                            pid: Long,
                            iterations: Int,
                            vOut: TimedVerification,
                            cOut: Performance,
                            xa: transactor.Transactor.Aux[IO, Unit]): Unit = {
    val tr = vOut.translation
    val vf = vOut.verification
    val in = vOut.instrumentation
    val cp = cOut
    val profiling = vOut.output.profiling
    (for {
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${tr.ninetyFifth}, ${tr.fifth}, ${tr.median}, ${tr.mean}, ${tr.stdev}, ${tr.minimum}, ${tr.maximum});".update.run
      tr_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${vf.ninetyFifth}, ${vf.fifth}, ${vf.median}, ${vf.mean}, ${vf.stdev}, ${vf.minimum}, ${vf.maximum});".update.run
      vf_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${in.ninetyFifth}, ${in.fifth}, ${in.median}, ${in.mean}, ${in.stdev}, ${in.minimum}, ${in.maximum});".update.run
      in_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${cp.ninetyFifth}, ${cp.fifth}, ${cp.median}, ${cp.mean}, ${cp.stdev}, ${cp.minimum}, ${cp.maximum});".update.run
      cp_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      r <- sql"CALL sp_UpdateStatic($vid, $hid, $pid, $tr_id, $vf_id, $in_id, $cp_id, ${profiling.nConjuncts}, ${profiling.nConjunctsEliminated});".update.run
    } yield r).transact(xa).unsafeRunSync()
  }

  def reserveProgramForMeasurement(
      version: Long,
      hardware: Long,
      workloads: List[Int],
      xa: DBConnection): Option[ReservedProgram] = {
    for (i <- workloads) {
      val reserved = (for {
        _ <- sql"""CALL sp_ReservePermutation($version, $hardware, $i, @perm, @perf, @mode);""".update.run
        perf_id <- sql"""SELECT @perf;""".query[Long].option
        perm <- sql"""SELECT * FROM permutations WHERE id = (SELECT @perm);"""
          .query[Permutation]
          .option
        mode <- sql"""SELECT @mode;"""
          .query[DynamicMeasurementMode.DynamicMeasurementMode]
          .option
      } yield (perf_id, perm, mode)).transact(xa).unsafeRunSync()
      reserved._1 match {
        case Some(perfIDReserved) =>
          reserved._2 match {
            case Some(permutationReserved) =>
              reserved._3 match {
                case Some(modeReserved) =>
                  Some(
                    ReservedProgram(permutationReserved,
                                    i,
                                    perfIDReserved,
                                    modeReserved))
                case None =>
              }
            case None =>
          }
        case None =>
      }
    }
    None
  }

  def completeProgramMeasurement(performanceID: Long,
                                 iterations: Int,
                                 p: Performance,
                                 xa: DBConnection) = {
    (for {
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES (${iterations}, ${p.ninetyFifth}, ${p.fifth}, ${p.median}, ${p.mean}, ${p.stdev}, ${p.minimum}, ${p.maximum});".update.run
      mid <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      r <- sql"UPDATE dynamic_performance SET measurement_id = $mid, last_updated = CURRENT_TIMESTAMP WHERE id = $performanceID;".update.run
    } yield r).transact(xa).unsafeRunSync()
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

  def logException(versionID: Long,
                   hardwareID: Long,
                   reserved: ReservedProgram,
                   mode: ErrorType,
                   errText: String,
                   timeElapsedSeconds: Long,
                   conn: DBConnection): Unit = {
    (for {
      _ <- sql"CALL sp_gr_Error($errText, $timeElapsedSeconds, $mode, @eid)".update.run
      eid <- sql"SELECT @eid".query[Long].unique
      _ <- sql"UPDATE static_performance SET error_id = $eid WHERE hardware_id = $hardwareID AND version_id = $versionID AND permutation_id = ${reserved.perm.id}".update.run
      u <- sql"UPDATE dynamic_performance SET error_id = $eid WHERE id = ${reserved.perfID}".update.run
    } yield u).transact(conn).unsafeRunSync()
  }
}