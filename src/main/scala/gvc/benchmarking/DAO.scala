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
import gvc.Config.{error, prettyPrintException}
import gvc.benchmarking.BenchmarkExecutor.ReservedProgram
import gvc.benchmarking.BenchmarkPopulator.md5sum
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.ErrorType.ErrorType
import gvc.benchmarking.Timing.TimedVerification

import scala.collection.mutable

class DBException(message: String) extends Exception(message)

object DAO {

  type DBConnection = Transactor.Aux[IO, Unit]

  object Names {
    val stressValues = "temporary_stress_values"
  }

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
    val Unknown = "unknown"
    val Weaving = "weaving"
  }

  case class GlobalConfiguration(timeoutMinutes: Long, maxPaths: Long)

  case class Identity(vid: Long, hid: Long, nid: Option[Long])

  case class Version(id: Long, versionName: String, dateAdded: String)

  case class Permutation(id: Long,
                         programID: Long,
                         permutationHash: Array[Byte],
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

  def connect(credentials: BenchmarkDBCredentials,
              config: BenchmarkingConfig): DBConnection = {
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
    sql"SELECT timeout_minutes, max_paths FROM global_configuration LIMIT 1"
      .query[GlobalConfiguration]
      .unique
      .transact(conn)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          "Unable to resolve global benchmarking configuration.",
          t)
      case Right(value) => value
    }
  }

  def addOrResolveIdentity(config: ExecutorConfig,
                           xa: DBConnection): Identity = {
    val hid = addOrResolveHardware(config.hardware, xa)
    val vid = addOrResolveVersion(config.version, xa)
    val nid = config.nickname match {
      case Some(value) => Some(addOrResolveNickname(value, xa))
      case None        => None
    }
    Identity(vid, hid, nid)
  }

  def addOrResolveNickname(name: String,
                           xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    val attemptedResult = (for {
      _ <- sql"CALL sp_gr_Nickname($name, @nn);".update.run
      nid <- sql"SELECT @nn;".query[Long].unique
    } yield nid)
      .transact(xa)
      .attempt
      .unsafeRunSync()
    attemptedResult match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve nickname $name", t)
      case Right(value) => value
    }
  }

  private def addOrResolveHardware(
      name: String,
      xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    (for {
      _ <- sql"CALL sp_gr_Hardware($name, @hw);".update.run
      hid <- sql"SELECT @hw;".query[Long].unique
    } yield hid)
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve hardware $name", t)
      case Right(value) => value
    }
  }

  private def addOrResolveVersion(
      name: String,
      xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    (for {
      _ <- sql"CALL sp_gr_Version($name, @ver);".update.run
      vid <- sql"SELECT @ver;".query[Long].unique
    } yield vid)
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve version $name", t)
      case Right(value) => value
    }
  }

  def resolveProgram(filename: String,
                     hash: String,
                     numLabels: Long,
                     xa: transactor.Transactor.Aux[IO, Unit]): Option[Long] = {
    sql"SELECT id FROM programs WHERE num_labels = $numLabels AND src_hash = $hash"
      .query[Option[Long]]
      .unique
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to resolve program $filename", t)
      case Right(value) => value
    }
  }

  def addOrResolveProgram(filename: java.nio.file.Path,
                          hash: String,
                          numLabels: Long,
                          xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    val name = filename.getFileName.toString
    (for {
      _ <- sql"CALL sp_gr_Program($name, $hash, $numLabels, @pid);".update.run
      pid <- sql"SELECT @pid;".query[Long].unique
    } yield pid)
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add program $filename", t)
      case Right(value) => value
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

  def resolveComponent(
      programID: Long,
      astLabel: ASTLabel,
      xa: transactor.Transactor.Aux[IO, Unit]): Option[Long] = {
    val contextName = astLabel.parent match {
      case Left(value)  => value.name
      case Right(value) => value.name
    }
    sql"SELECT id FROM components WHERE context_name = $contextName AND spec_index = ${astLabel.specIndex} AND spec_type = ${astLabel.specType} AND expr_index = ${astLabel.exprIndex} AND expr_type = ${astLabel.exprType} AND program_id = $programID;"
      .query[Option[Long]]
      .unique
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to resolve component ${astLabel.hash}", t)
      case Right(value) => value
    }
  }

  def addOrResolveComponent(programID: Long,
                            astLabel: ASTLabel,
                            xa: transactor.Transactor.Aux[IO, Unit]): Long = {
    val contextName = astLabel.parent match {
      case Left(value)  => value.name
      case Right(value) => value.name
    }
    (for {
      _ <- sql"CALL sp_gr_Component($programID, $contextName, ${astLabel.specType}, ${astLabel.specIndex}, ${astLabel.exprType}, ${astLabel.exprIndex}, @comp);".update.run
      cid <- sql"SELECT @comp;".query[Long].unique
    } yield cid).transact(xa).attempt.unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to add or resolve component ${astLabel.hash}",
          t)
      case Right(value) => value
    }
  }

  def resolvePermutation(permID: Long,
                         xa: DBConnection): Option[Permutation] = {
    sql"SELECT * FROM permutations WHERE id = $permID;"
      .query[Option[Permutation]]
      .unique
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to resolve permutation $permID", t)
      case Right(value) => value
    }
  }

  def addOrResolvePermutation(programID: Long,
                              permutationHash: Array[Byte],
                              xa: DBConnection): Long = {

    (for {
      _ <- sql"""CALL sp_gr_Permutation($programID, $permutationHash, @perm);""".update.run
      pid <- sql"""SELECT @perm;""".query[Long].unique
    } yield pid).transact(xa).attempt.unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve permutation $programID",
                             t)
      case Right(value) => value
    }
  }

  def getNumberOfPaths(programID: Long, xa: DBConnection): Int = {
    sql"SELECT COUNT(*) FROM paths WHERE program_id = $programID"
      .query[Int]
      .unique
      .transact(xa)
      .attempt
      .unsafeRunSync() match {
      case Left(value) =>
        prettyPrintException(
          s"Unable to get path count for program ID $programID",
          value)
      case Right(value) => value
    }
  }

  def updateStaticProfiling(id: Identity,
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
    val nn = id.nid match {
      case Some(value) => value.toString
      case None        => "NULL"
    }
    val attemptedUpdate = (for {
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${tr.ninetyFifth}, ${tr.fifth}, ${tr.median}, ${tr.mean}, ${tr.stdev}, ${tr.minimum}, ${tr.maximum});".update.run
      tr_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${vf.ninetyFifth}, ${vf.fifth}, ${vf.median}, ${vf.mean}, ${vf.stdev}, ${vf.minimum}, ${vf.maximum});".update.run
      vf_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${in.ninetyFifth}, ${in.fifth}, ${in.median}, ${in.mean}, ${in.stdev}, ${in.minimum}, ${in.maximum});".update.run
      in_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${cp.ninetyFifth}, ${cp.fifth}, ${cp.median}, ${cp.mean}, ${cp.stdev}, ${cp.minimum}, ${cp.maximum});".update.run
      cp_id <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      r <- sql"CALL sp_UpdateStatic(${id.vid}, ${id.hid}, $nn, $pid, $tr_id, $vf_id, $in_id, $cp_id, ${profiling.nConjuncts}, ${profiling.nConjunctsEliminated});".update.run
    } yield r).transact(xa).attempt.unsafeRunSync()
    attemptedUpdate match {
      case Left(value) =>
        prettyPrintException(
          s"Unable to update static compilation performance for gradual verification of permutation $pid",
          value)
      case Right(_) =>
    }
  }

  def reserveProgramForMeasurement(
      id: Identity,
      worklist: String,
      xa: DBConnection): Option[ReservedProgram] = {
    val nn = id.nid match {
      case Some(value) => value.toString
      case None        => "NULL"
    }
    val reservedAttempt = (for {
      _ <- sql"""CALL sp_ReservePermutation(${id.vid}, ${id.hid}, $nn, $worklist, @perm, @mode);""".update.run
      perm <- sql"""SELECT * FROM permutations WHERE id = (SELECT @perm);"""
        .query[Option[Permutation]]
        .unique
      mode <- sql"""SELECT @mode;"""
        .query[Option[Long]]
        .unique
      worklist <- sql"""SELECT * FROM filtered_stress ORDER BY filtered_stress.stress;"""
        .query[Int]
        .to[List]
    } yield (worklist, perm, mode)).transact(xa).attempt.unsafeRunSync()
    reservedAttempt match {
      case Left(value) =>
        prettyPrintException(
          "Unable to reserve a new program for benchmarking.",
          value)
      case Right(reserved) =>
        if (reserved._1.nonEmpty) {
          reserved._2 match {
            case Some(p) =>
              reserved._3 match {
                case Some(m) => Some(ReservedProgram(p, reserved._1, m))
                case None =>
                  error(
                    "Both a valid set of workloads and a permutation were resolved, but a measurement mode wasn't resolved.")
              }
            case None =>
              error(
                "A valid set of workloads was resolved, but a permutation wasn't resolved. ")
          }
        } else {
          None
        }
    }
  }

  def completeProgramMeasurement(id: Identity,
                                 reserved: ReservedProgram,
                                 workload: Int,
                                 iterations: Int,
                                 p: Performance,
                                 xa: DBConnection): Unit = {
    val nicknameResolved = id.nid match {
      case Some(value) => value.toString
      case None        => "NULL"
    }
    val result = (for {
      _ <- sql"INSERT INTO measurements (iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum) VALUES ($iterations, ${p.ninetyFifth}, ${p.fifth}, ${p.median}, ${p.mean}, ${p.stdev}, ${p.minimum}, ${p.maximum});".update.run
      mid <- sql"SELECT LAST_INSERT_ID();".query[Long].unique
      r <- sql"""UPDATE dynamic_performance SET measurement_id = $mid, last_updated = CURRENT_TIMESTAMP
        WHERE permutation_id = ${reserved.perm.id}
          AND version_id = ${id.vid}
          AND nickname_id = $nicknameResolved
          AND hardware_id = ${id.hid}
          AND dynamic_measurement_type = ${reserved.measurementMode}
          AND stress = $workload;
        """.update.run
    } yield r).transact(xa).attempt.unsafeRunSync()
    result match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to update performance measurement for permutation ${reserved.perm.id}.",
          t)
      case Right(_) =>
    }
  }

  def containsPath(programID: Long,
                   pathHash: Array[Byte],
                   xa: DBConnection): Boolean = {
    sql"SELECT COUNT(*) > 0 FROM paths WHERE program_id = $programID AND path_hash = $pathHash;"
      .query[Boolean]
      .unique
      .transact(xa)
      .unsafeRunSync()
  }

  class PathQueryCollection(hash: Array[Byte],
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

  def logException(id: Identity,
                   reserved: ReservedProgram,
                   mode: ErrorType,
                   errText: String,
                   timeElapsedSeconds: Long,
                   conn: DBConnection): Unit = {

    val nn = id.nid match {
      case Some(value) => value.toString
      case None        => "NULL"
    }
    val errorHash = md5sum(errText)
    (for {
      _ <- sql"CALL sp_gr_Error($errorHash, $errText, $timeElapsedSeconds, $mode, @eid)".update.run
      eid <- sql"SELECT @eid".query[Long].unique
      _ <- sql"UPDATE static_performance SET error_id = $eid WHERE hardware_id = ${id.hid} AND version_id = ${id.vid} AND nickname_id = $nn AND permutation_id = ${reserved.perm.id}".update.run
      u <- sql"UPDATE dynamic_performance SET error_id = $eid WHERE hardware_id = ${id.hid} AND version_id = ${id.vid} AND nickname_id = $nn AND permutation_id = ${reserved.perm.id}".update.run
    } yield u).transact(conn).attempt.unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to log error with mode $mode.\n $errText",
                             t)
      case Right(_) =>
    }
  }

  case class CompletionMetadata(versionName: String,
                                hardwareName: String,
                                srcFilename: String,
                                measurementMode: String,
                                totalCompleted: Long,
                                total: Long,
                                errorType: Option[String],
                                errorCount: Option[Long],
                                stress: Long)

  def listPerformanceResults(conn: DBConnection): List[CompletionMetadata] = {
    sql"""SELECT version_name,
           hardware_name,
           src_filename,
           measurement_type,
           total_completed,
           total_perms,
           error_type,
           error_count,
           completion.stress
    FROM (SELECT *
          FROM (SELECT program_id, COUNT(permutations.id) as total_perms
                FROM permutations
                         INNER JOIN programs p on permutations.program_id = p.id

                GROUP BY program_id) as tblA
                   INNER JOIN (SELECT program_id            as pid,
                                      src_filename,
                                      version_name,
                                      version_id,
                                      hardware_name,
                                      hardware_id,
                                      measurement_type,
                                      dmt.id,
                                      stress,
                                      COUNT(measurement_id) as total_completed

                               FROM versions
                                        INNER JOIN dynamic_performance dp on versions.id = dp.version_id
                                        INNER JOIN permutations p on dp.permutation_id = p.id
                                        INNER JOIN programs p2 on p.program_id = p2.id
                                        INNER JOIN dynamic_measurement_types dmt on dp.dynamic_measurement_type = dmt.id
                                        INNER JOIN hardware h on dp.hardware_id = h.id
                               WHERE measurement_id IS NOT NULL
                               GROUP BY program_id, src_filename, version_name, hardware_name, measurement_type, stress) as tblB
                              on tblA.program_id = tblB.pid) as completion
             LEFT OUTER JOIN (SELECT version_id,
                                     hardware_id,
                                     program_id,
                                     dynamic_measurement_type,
                                     error_type,
                                     stress,
                                     COUNT(DISTINCT error_id) as error_count
                              FROM dynamic_performance
                                       INNER JOIN permutations p on dynamic_performance.permutation_id = p.id
                                       INNER JOIN error_occurrences e on dynamic_performance.error_id = e.id
                              GROUP BY version_id, hardware_id, program_id, dynamic_measurement_type, error_type, stress) as errors
                             ON completion.program_id = errors.program_id
                                 AND completion.version_id = errors.version_id AND
                                completion.program_id = errors.program_id AND
                                completion.id = errors.dynamic_measurement_type;"""
      .query[CompletionMetadata]
      .to[List]
      .transact(conn)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to resolve completion data.", t)
      case Right(value) => value
    }
  }

  case class ResolvedMeasurementMode(id: Long, modeType: String)

  def resolveDynamicModes(
      conn: DBConnection): Map[Long, DynamicMeasurementMode] = {
    sql"""SELECT id, measurement_type FROM dynamic_measurement_types;"""
      .query[ResolvedMeasurementMode]
      .to[List]
      .transact(conn)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          "Unable to resolve list of dynamic measurement modes.",
          t)
      case Right(value) => value.map(rm => rm.id -> rm.modeType).toMap
    }
  }

  def listErrors(conn: DBConnection): List[PermutationError] = {
    sql"""SELECT permutation_id, version_name, src_filename, measurement_type, time_elapsed_seconds, error_type, error_desc
         FROM error_occurrences
             INNER JOIN dynamic_performance ON dynamic_performance.error_id = error_occurrences.id
             INNER JOIN error_contents ON error_occurrences.error_contents_id = error_contents.id
             INNER JOIN versions ON dynamic_performance.version_id = versions.id
INNER JOIN permutations p on dynamic_performance.permutation_id = p.id
INNER JOIN programs p2 on p.program_id = p2.id
INNER JOIN dynamic_measurement_types dmt on dynamic_performance.dynamic_measurement_type = dmt.id;"""
      .query[PermutationError]
      .to[List]
      .transact(conn)
      .attempt
      .unsafeRunSync() match {
      case Left(t)      => prettyPrintException("Unable to resolve error list.", t)
      case Right(value) => value
    }
  }

  case class PermutationError(pid: Long,
                              versionName: String,
                              programName: String,
                              measurementMode: String,
                              timeSeconds: Long,
                              errorType: String,
                              errorDesc: String)
}
