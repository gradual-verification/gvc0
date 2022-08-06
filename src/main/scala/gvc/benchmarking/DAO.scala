package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
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
import gvc.benchmarking.DAO.StaticMeasurementMode.StaticMeasurementMode
import gvc.benchmarking.Timing.TimedVerification

import java.sql.SQLTransactionRollbackException
import scala.collection.mutable

class DBException(message: String) extends Exception(message)

object DAO {

  case class DBConnection(gConfig: GlobalConfiguration,
                          dynamicModes: Map[Long, DynamicMeasurementMode],
                          staticModes: Map[StaticMeasurementMode, Long],
                          xa: Transactor.Aux[IO, Unit])

  object DynamicMeasurementMode {
    type DynamicMeasurementMode = String
    val Gradual = "gradual"
    val Framing = "framing"
    val Dynamic = "dynamic"
  }

  object StaticMeasurementMode {
    type StaticMeasurementMode = String
    val Instrumentation = "instrumentation"
    val Compilation = "compilation"
    val Verification = "verification"
    val Translation = "translation"
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
                         permutationHash: String,
                         permutationContents: Array[Byte],
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

    val gConfig = resolveGlobalConfiguration(connection)
    val dynamicModes = resolveDynamicModes(connection)
    val staticModes = resolveStaticModes(connection)
    DBConnection(gConfig, dynamicModes, staticModes, connection)
  }

  private def resolveGlobalConfiguration(
      conn: Transactor.Aux[IO, Unit]): GlobalConfiguration = {
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

  private case class ResolvedMeasurementMode(id: Long, modeType: String)

  private def resolveDynamicModes(
      conn: Transactor.Aux[IO, Unit]): Map[Long, DynamicMeasurementMode] = {
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

  private def resolveStaticModes(
      conn: Transactor.Aux[IO, Unit]
  ): Map[StaticMeasurementMode, Long] = {
    sql"""SELECT id, measurement_type FROM static_measurement_types;"""
      .query[ResolvedMeasurementMode]
      .to[List]
      .transact(conn)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          "Unable to resolve list of static measurement modes.",
          t)
      case Right(value) => value.map(rm => rm.modeType -> rm.id).toMap
    }
  }

  def addProgramWorkloadMappings(programID: Long,
                                 workloads: List[Int],
                                 c: DBConnection): Unit = {
    case class WorkloadEntry(pid: Long, stressValue: Int)
    Update[WorkloadEntry](
      s"INSERT INTO stress_assignments (program_id, stress) VALUES (?, ?);")
      .updateMany(
        for {
          w <- workloads
        } yield WorkloadEntry(programID, w)
      )
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to add workload entries for PID=$programID",
          t)
      case Right(_) =>
    }
  }

  def addOrResolveIdentity(config: ExecutorConfig,
                           c: DBConnection): Identity = {
    val hid = addOrResolveHardware(config.hardware, c)
    val vid = addOrResolveVersion(config.version, c)
    val nid = config.nickname match {
      case Some(value) => Some(addOrResolveNickname(value, c))
      case None        => None
    }
    Identity(vid, hid, nid)
  }

  def addOrResolveNickname(name: String, c: DBConnection): Long = {
    sql"CALL sp_gr_Nickname($name);"
      .query[Long]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve nickname $name", t)
      case Right(value) => value
    }
  }

  private def addOrResolveHardware(name: String, c: DBConnection): Long = {
    sql"CALL sp_gr_Hardware($name);"
      .query[Long]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve hardware $name", t)
      case Right(value) => value
    }
  }

  private def addOrResolveVersion(name: String, c: DBConnection): Long = {
    sql"CALL sp_gr_Version($name);"
      .query[Long]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve version $name", t)
      case Right(value) => value
    }
  }

  def resolveProgram(hash: String,
                     numLabels: Long,
                     c: DBConnection): Option[Long] = {
    sql"SELECT id FROM programs WHERE num_labels = $numLabels AND src_hash = $hash"
      .query[Option[Long]]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(_)      => None
      case Right(value) => value
    }
  }

  def addOrResolveProgram(filename: java.nio.file.Path,
                          hash: String,
                          numLabels: Long,
                          c: DBConnection): Long = {
    sql"CALL sp_gr_Program(${filename.getFileName.toString}, $hash, $numLabels);"
      .query[Long]
      .unique
      .transact(c.xa)
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

  def resolveComponent(programID: Long,
                       astLabel: ASTLabel,
                       conn: DBConnection): Option[Long] = {
    val contextName = astLabel.parent match {
      case Left(value)  => value.name
      case Right(value) => value.name
    }
    sql"""SELECT id FROM components
                WHERE context_name = $contextName
                    AND spec_index = ${astLabel.specIndex}
                    AND spec_type = ${astLabel.specType}
                    AND expr_index = ${astLabel.exprIndex}
                    AND expr_type = ${astLabel.exprType}
                    AND program_id = $programID;"""
      .query[Option[Long]]
      .unique
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to resolve component ${astLabel.hash}", t)
      case Right(value) => value
    }
  }

  def addOrResolveComponent(programID: Long,
                            astLabel: ASTLabel,
                            c: DBConnection): Long = {
    val contextName = astLabel.parent match {
      case Left(value)  => value.name
      case Right(value) => value.name
    }
    sql"""CALL sp_gr_Component($programID, $contextName, ${astLabel.specType},
       ${astLabel.specIndex}, ${astLabel.exprType}, ${astLabel.exprIndex});"""
      .query[Long]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to add or resolve component ${astLabel.hash}",
          t)
      case Right(value) => value
    }
  }

  def resolvePermutation(permID: Long, c: DBConnection): Option[Permutation] = {
    sql"SELECT * FROM permutations WHERE id = $permID;"
      .query[Option[Permutation]]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to resolve permutation $permID", t)
      case Right(value) => value
    }
  }

  def addOrResolvePermutation(programID: Long,
                              checksum: String,
                              permutationContents: Array[Byte],
                              c: DBConnection): Long = {
    sql"""CALL sp_gr_Permutation($programID, $checksum, $permutationContents);"""
      .query[Long]
      .to[List]
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to add or resolve permutation $programID",
                             t)
      case Right(value) =>
        if (value.size != 1) {
          error("More than one resolved permutation was recorded.")
        } else {
          value.head
        }
    }
  }

  def getNumberOfPaths(programID: Long, c: DBConnection): Int = {
    sql"SELECT COUNT(*) FROM paths WHERE program_id = $programID"
      .query[Int]
      .unique
      .transact(c.xa)
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
                            c: DBConnection): Unit = {
    (List(vOut.translation, vOut.verification, vOut.instrumentation, cOut) zip
      List(StaticMeasurementMode.Translation,
           StaticMeasurementMode.Verification,
           StaticMeasurementMode.Instrumentation,
           StaticMeasurementMode.Compilation))
      .foreach(p => {
        val m = p._1
        (for {
          mid <- sql"""CALL sp_AddMeasurement($iterations, ${m.ninetyFifth}, ${m.fifth},
               ${m.median}, ${m.mean}, ${m.stdev}, ${m.minimum}, ${m.maximum});"""
            .query[Long]
            .unique
          u <- sql"CALL sp_UpdateStaticPerformance(${id.vid}, ${id.hid}, ${id.nid}, $pid, $mid, ${c
            .staticModes(p._2)});".update.run
        } yield u).transact(c.xa).attempt.unsafeRunSync() match {
          case Left(t) =>
            prettyPrintException(
              s"Failed to update static performance for ${p._2}, PID=$pid",
              t)
          case Right(_) =>
        }
      })
    sql"""CALL sp_UpdateStaticConjuncts(${id.vid}, $pid, ${vOut.output.profiling.nConjuncts},
          ${vOut.output.profiling.nConjunctsEliminated})""".update.run
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to update static verification profiling information for PID=$pid",
          t)
      case Right(_) =>
    }

  }

  case class ReservedProgramEntry(permID: Long,
                                  stress: Int,
                                  measurementID: Long)

  def reserveProgramForMeasurement(id: Identity,
                                   c: DBConnection): Option[ReservedProgram] = {
    Output.info(s"Beginning reservation query...")
    val startTime = System.nanoTime()
    var finished = false
    var result: Option[ReservedProgram] = None
    while (!finished) {
      finished = true
      sql"CALL sp_ReservePermutation(${id.vid}, ${id.hid}, ${id.nid});"
        .query[ReservedProgramEntry]
        .to[List]
        .transact(c.xa)
        .attempt
        .unsafeRunSync() match {
        case Left(t) =>
          t match {
            case _: SQLTransactionRollbackException =>
              Output.info("Deadlock detected; pausing and retrying...")
              Thread.sleep(50)
              finished = false
            case _ =>
              prettyPrintException("Unable to reserve program for benchmarking",
                                   t)
          }
        case Right(value) =>
          if (value.isEmpty) {
            finished = true
          } else {
            val workloads = value.map(v => v.stress)
            val permID = value.head.permID
            sql"SELECT * FROM permutations WHERE id = $permID;"
              .query[Permutation]
              .unique
              .transact(c.xa)
              .attempt
              .unsafeRunSync() match {
              case Left(t) =>
                prettyPrintException(
                  s"Unable to resolve reserved permutation ID=$permID",
                  t)
              case Right(perm) =>
                result = Some(
                  ReservedProgram(perm, workloads, value.head.measurementID))
                finished = true
            }
          }
      }
    }
    val stopTime = System.nanoTime()
    val differenceInSeconds = Math
      .round(((stopTime - startTime).toDouble / Math.pow(10, 9)) * 100)
      .toDouble / 100
    Output.info(s"Finished reservation query in $differenceInSeconds sec.")
    result
  }

  def completeProgramMeasurement(id: Identity,
                                 reserved: ReservedProgram,
                                 workload: Long,
                                 iterations: Int,
                                 p: Performance,
                                 c: DBConnection): Unit = {

    val result = (for {
      mid <- sql"""CALL sp_AddMeasurement($iterations, ${p.ninetyFifth}, ${p.fifth}, ${p.median}, ${p.mean},
          ${p.stdev}, ${p.minimum}, ${p.maximum});"""
        .query[Long]
        .unique
      r <- sql"""UPDATE dynamic_performance SET measurement_id = $mid, last_updated = CURRENT_TIMESTAMP
          WHERE permutation_id = ${reserved.perm.id}
            AND version_id = ${id.vid}
            AND nickname_id = ${id.nid}
            AND hardware_id = ${id.hid}
            AND measurement_type_id = ${reserved.measurementMode}
            AND stress = $workload
          """.update.run
    } yield r).transact(c.xa).attempt.unsafeRunSync()
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
                   c: DBConnection): Boolean = {
    sql"SELECT COUNT(*) > 0 FROM paths WHERE program_id = $programID AND path_hash = $pathHash;"
      .query[Boolean]
      .unique
      .transact(c.xa)
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

    def exec(c: DBConnection): Unit = {
      val massUpdate = for {
        pid <- sql"CALL sp_gr_Path($programID, $hash);".query[Long].unique
        _ <- sql"""INSERT INTO steps (permutation_id, level_id, path_id)
               VALUES ($bottomPermutationID, 0, $pid)""".update.run
        v <- Update[Step](
          s"INSERT INTO steps (permutation_id, level_id, component_id, path_id) VALUES (?, ?, ?, ?)")
          .updateMany(
            this.steps.indices
              .map(i => Step(this.steps(i)._1, i + 1, this.steps(i)._2, pid))
              .toList)
      } yield v
      massUpdate.transact(c.xa).unsafeRunSync()
    }
  }

  def logException(id: Identity,
                   reserved: ReservedProgram,
                   mode: ErrorType,
                   errText: String,
                   conn: DBConnection): Unit = {
    val errorHash = md5sum(errText)
    val eid = sql"CALL sp_gr_Error($errorHash, $errText, $mode);"
      .query[Long]
      .unique
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to resolve error ID for exception '$errText'",
          t)
      case Right(value) => value
    }
    sql"""UPDATE static_performance SET error_id = $eid
                              WHERE hardware_id = ${id.hid}
                                AND version_id = ${id.vid}
                                AND nickname_id = ${id.nid}
                                AND permutation_id = ${reserved.perm.id}""".update.run
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to update static performance entry with error ID for exception '$errText', ID=$eid",
          t)
      case Right(_) =>
    }
    reserved.workloads.foreach(w => {
      sql"""UPDATE dynamic_performance SET error_id = $eid
           WHERE permutation_id = ${reserved.perm.id}
             AND stress = $w
             AND version_id = ${id.vid}
             AND hardware_id = ${id.hid}
             AND nickname_id = ${id.nid};""".update.run
        .transact(conn.xa)
        .attempt
        .unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            s"Unable to update results entry with error ID for exception '$errText', ID=$eid, stress=$w",
            t)
        case Right(_) =>
      }
    })
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

}
