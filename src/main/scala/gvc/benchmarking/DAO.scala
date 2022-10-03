package gvc.benchmarking

import doobie._
import doobie.implicits._
import cats.effect.IO
import doobie._
import doobie.implicits._
import cats.effect.unsafe.implicits.global
import cats.free.Free
import doobie.free.connection
import gvc.CC0Wrapper.Performance
import gvc.Config.{error, prettyPrintException}
import gvc.benchmarking.BenchmarkExecutor.{ReservedProgram, StressTable}
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
                          xa: Transactor.Aux[IO, Unit],
                          retries: Int)

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
    val ExecutionTimeout = "dynamic-timeout"
    val VerificationTimeout = "static-timeout"
    val Unknown = "unknown"
    val Weaving = "weaving"
  }

  object Defaults {
    val DefaultBenchmarkName = "default"
    val DefaultBenchmarkIncrements: List[Int] = List(20, 40, 60, 80)
    val retries = 5
  }

  case class GlobalConfiguration(maxPaths: Long)

  case class Identity(vid: Long, hwid: Long, nid: Long)

  case class Permutation(id: Long,
                         programID: Long,
                         permutationHash: String,
                         permutationContents: Array[Byte],
                         dateAdded: String)

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
    DBConnection(gConfig,
                 dynamicModes,
                 staticModes,
                 connection,
                 retries = Defaults.retries)
  }

  private def resolveGlobalConfiguration(
      conn: Transactor.Aux[IO, Unit]): GlobalConfiguration = {
    sql"SELECT max_paths FROM global_configuration LIMIT 1"
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

  def addOrResolveIdentity(config: ExecutorConfig,
                           c: DBConnection): Identity = {
    val hid = addOrResolveHardware(config.hardware, c)
    val vid = addOrResolveVersion(config.version, c)
    val nid = addOrResolveNickname(config.nickname, c)
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

  case class IdentifiedProgram(filename: String, srcHash: String)

  def resolveProgram(id: Long, c: DBConnection): Option[IdentifiedProgram] = {
    sql"SELECT src_filename, src_hash FROM programs WHERE id = $id;"
      .query[Option[IdentifiedProgram]]
      .unique
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(_)      => None
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

  def resolveProgramName(id: Long, c: DBConnection): Option[String] = {
    sql"SELECT src_filename FROM programs WHERE id=$id;"
      .query[Option[String]]
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

    val basenameWithExtension = filename.getFileName.toString
    val extensionRemoved = basenameWithExtension.substring(
      0,
      basenameWithExtension.lastIndexOf(".c0"))
    sql"CALL sp_gr_Program($extensionRemoved, $hash, $numLabels);"
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
          u <- sql"CALL sp_UpdateStaticPerformance(${id.vid}, ${id.hwid}, ${id.nid}, $pid, $mid, ${c
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
                                   table: StressTable,
                                   ec: ExecutorConfig,
                                   c: DBConnection): Option[ReservedProgram] = {
    var result: Option[ReservedProgram] = None
    var maxRetries = c.retries
    while (maxRetries > 0) {
      maxRetries -= 1
      (for {
        _ <- Utilities.createTemporaryStressValueTable(table)
        sp <- sql"""CALL sp_ReservePermutation(
                    ${id.vid},
                    ${id.hwid},
                    ${id.nid},
                    ${ec.modifiers.exclusiveMode},
                    ${ec.timeoutMinutes},
                    ${ec.modifiers.onlyBenchmark},
                    ${ec.modifiers.nicknameSensitivity}
            );"""
          .query[ReservedProgramEntry]
          .to[List]
      } yield sp)
        .transact(c.xa)
        .attempt
        .unsafeRunSync() match {
        case Left(t) =>
          t match {
            case _: SQLTransactionRollbackException =>
              Output.info("Deadlock detected; pausing and retrying...")
              Thread.sleep(50)
            case _ =>
              prettyPrintException("Unable to reserve program for benchmarking",
                                   t)
          }
        case Right(value) =>
          if (value.nonEmpty) {
            maxRetries = -1
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
            }
          }
      }
    }
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
            AND hardware_id = ${id.hwid}
            AND measurement_type_id = ${reserved.measurementMode}
            AND stress = $workload
          """.update.run
    } yield r).transact(c.xa).attempt.unsafeRunSync()
    result match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to update performance measurement for permutation ${reserved.perm.id}.",
          t)
      case Right(r) =>
        if (r > 1) {
          error(
            "More than one performance record was updated with the same result")
        }
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

  def logStaticException(id: Identity,
                         reserved: ReservedProgram,
                         eid: Long,
                         conn: DBConnection): Unit = {

    sql"""INSERT INTO static_errors (error_id, permutation_id, version_id, hardware_id, nickname_id)
            VALUES ($eid, ${reserved.perm.id}, ${id.vid}, ${id.hwid}, ${id.nid});""".update.run
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to update static performance entry for permutation ID=${reserved.perm.id} with error ID=$eid",
          t)
      case Right(_) =>
    }
  }

  def logDynamicException(id: Identity,
                          reserved: ReservedProgram,
                          eid: Long,
                          stress: List[Int],
                          conn: DBConnection,
  ): Unit = {
    reserved.workloads.foreach(w => {
      sql"""INSERT INTO dynamic_errors (error_id, permutation_id, version_id, hardware_id, nickname_id, stress, measurement_type_id)
      VALUES ($eid, ${reserved.perm.id}, ${id.vid}, ${id.hwid}, ${id.nid}, $w, ${reserved.measurementMode});""".update.run
        .transact(conn.xa)
        .attempt
        .unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            s"Unable to update results entry with error ID=$eid for permutation ID=${reserved.perm.id}, stress=$w",
            t)
        case Right(_) =>
      }
    })
  }

  def resolveException(mode: ErrorType,
                       errText: String,
                       conn: DBConnection): Long = {
    val errorHash = md5sum(errText)
    sql"CALL sp_gr_Error($errorHash, $errText, $mode);"
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
  }

  def populateIncrementalBenchmark(benchmarkName: String,
                                   increments: List[Int],
                                   c: DBConnection): Unit = {
    case class ProgramStepCount(programID: Long, numSteps: Long)
    case class BenchmarkEntry(levelID: Long, pathID: Long, programID: Long)
    val benchmarkEntries: List[BenchmarkEntry] =
      sql"SELECT program_id, COUNT(DISTINCT components.id) FROM components GROUP BY program_id;"
        .query[ProgramStepCount]
        .to[List]
        .transact(c.xa)
        .attempt
        .unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            "Unable to resolve step count per path for each program.",
            t)
        case Right(programList) => {
          programList.flatMap(p => {
            val indices =
              increments.map(i =>
                Math.round(i.toDouble / 100 * (p.numSteps - 1)).toInt)
            val minPathIndex =
              sql"SELECT MIN(id) FROM paths WHERE program_id = ${p.programID};"
                .query[Option[Int]]
                .unique
                .transact(c.xa)
                .attempt
                .unsafeRunSync() match {
                case Left(t) =>
                  prettyPrintException(
                    s"Unable to resolve minimum path ID for program ID=${p.programID}",
                    t)
                case Right(value) =>
                  value match {
                    case Some(value) => value
                    case None =>
                      error(
                        s"No paths have been entered for program ID=${p.programID}")
                  }
              }
            indices.map(idc => {
              BenchmarkEntry(idc, minPathIndex, p.programID)
            })
          })
        }
      }
    (for {
      bid <- sql"CALL sp_ResetBenchmark($benchmarkName, ${increments.mkString(",")});"
        .query[Long]
        .unique
      u <- Update[BenchmarkEntry](
        s"""INSERT INTO benchmark_membership (benchmark_id, permutation_id)
           | SELECT $bid, permutations.id FROM permutations INNER JOIN steps s on permutations.id = s.permutation_id
           | WHERE s.level_id = ? AND s.path_id = ? AND permutations.program_id = ?;""".stripMargin)
        .updateMany(
          benchmarkEntries
        )
    } yield u).transact(c.xa).attempt.unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to complete benchmark population query.",
                             t)
      case Right(_) =>
    }
  }

  def getErrorList(vid: Long, hid: Long, conn: DBConnection): String = {
    case class ErrorEntry(programID: Long,
                          permutationID: Long,
                          errorType: String,
                          occurredDuring: String,
                          measurementType: String,
                          errorDesc: String,
                          errorDate: String)

    sql"""SELECT program_id, permutation_id, error_type, occurred_during, measurement_type, error_desc, error_date
            FROM all_errors
            WHERE version_id = $vid AND hardware_id = $hid;"""
      .query[ErrorEntry]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          s"Unable to resolve versions for VID=$vid, HID=$hid",
          t)
      case Right(eList) =>
        eList
          .map(
            e =>
              List(e.programID,
                   e.permutationID,
                   e.errorType,
                   e.occurredDuring,
                   e.measurementType,
                   e.errorDesc,
                   e.errorDate).mkString(","))
          .mkString("\n")
    }
  }

  def resolveVersion(name: String, c: DBConnection): Option[Long] = {
    sql"SELECT id FROM versions WHERE version_name = $name;"
      .query[Long]
      .option
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to query for version '$name'", t)
      case Right(value) => value
    }
  }

  case class CompletedBenchmark(version: String,
                                hardware: String,
                                benchmark: String,
                                stress: Int,
                                measurementMode: String,
  )

  def getCompletedBenchmarks(c: DBConnection): List[CompletedBenchmark] = {

    sql"""SELECT version_name, hardware_name, benchmark_name, stress, measurement_type
         FROM completed_benchmarks cb
             INNER JOIN versions v ON cb.version_id = v.id
             INNER JOIN hardware ON cb.hardware_id = hardware.id
             INNER JOIN benchmarks ON cb.benchmark_id = benchmarks.id
             INNER JOIN dynamic_measurement_types dmt on cb.measurement_type_id = dmt.id;"""
      .query[CompletedBenchmark]
      .to[List]
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(
          "Unable to acquire list of completed preconfigured benchmarks.",
          t)
      case Right(value) => value
    }
  }

  def resolveHardware(name: String, c: DBConnection): Option[Long] = {
    sql"SELECT id FROM hardware WHERE hardware_name = $name;"
      .query[Long]
      .option
      .transact(c.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException(s"Unable to query for hardware '$name'", t)
      case Right(value) => value
    }
  }

  case class CompletedPathMetadata(version: String,
                                   hardware: String,
                                   program: String,
                                   workload: Int,
                                   measurementMode: String,
                                   num_paths: Int)
      extends IdentifiedMetadata

  def getCompletedPathList(conn: DBConnection): List[CompletedPathMetadata] = {
    sql"""SELECT version_name, hardware_name, src_filename, stress, measurement_type, COUNT(DISTINCT completed_paths.path_id)
        FROM completed_paths
                 INNER JOIN paths ON completed_paths.path_id = paths.id
                 INNER JOIN programs p2 on paths.program_id = p2.id
                 INNER JOIN versions v ON completed_paths.version_id = v.id
                 INNER JOIN hardware h ON completed_paths.hardware_id = h.id
        INNER JOIN dynamic_measurement_types dmt on completed_paths.measurement_type_id = dmt.id
        GROUP BY version_name, hardware_name, src_filename, stress, measurement_type;"""
      .query[CompletedPathMetadata]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to get list of completed paths", t)
      case Right(value) => value
    }
  }

  case class StaticTimingMetadata(program: String,
                                  version: String,
                                  hardware: String,
                                  max: Int,
                                  mean: Double)
      extends IdentifiedMetadata

  sealed trait IdentifiedMetadata {
    def program: String

    def version: String

    def hardware: String
  }

  def getStaticTiming(conn: DBConnection): List[StaticTimingMetadata] = {
    sql"""SELECT src_filename, version_name, hardware_name, max, mean
    FROM static_verification_times
             INNER JOIN versions v ON static_verification_times.version_id = v.id
             INNER JOIN hardware h ON static_verification_times.hardware_id = h.id
        INNER JOIN programs p on static_verification_times.program_id = p.id;"""
      .query[StaticTimingMetadata]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to get list of completed programs", t)
      case Right(value) => value
    }
  }

  case class CompletedProgramMetadata(program: String,
                                      version: String,
                                      hardware: String,
                                      stress: Int,
                                      measurementType: String,
                                      completed: Int,
                                      staticErrored: Int,
                                      dynamicErrored: Int,
                                      total: Int)
      extends IdentifiedMetadata

  def getCompletedProgramList(
      conn: DBConnection): List[CompletedProgramMetadata] = {
    sql"""SELECT src_filename, version_name, hardware_name, stress, measurement_type, completed, static_errored, dynamic_errored, total
    FROM completed_programs
             INNER JOIN versions v ON completed_programs.version_id = v.id
             INNER JOIN hardware h ON completed_programs.hardware_id = h.id
             INNER JOIN programs p on completed_programs.program_id = p.id
    INNER JOIN dynamic_measurement_types dmt on completed_programs.measurement_type_id = dmt.id"""
      .query[CompletedProgramMetadata]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to get list of completed programs", t)
      case Right(value) => value
    }
  }

  case class BenchmarkMetadata(name: String, desc: String, numPrograms: Int)

  def getBenchmarkList(conn: DBConnection): List[BenchmarkMetadata] = {
    sql"""SELECT benchmark_name, benchmark_desc, num_programs
                FROM (SELECT benchmark_id, COUNT(*) AS num_programs
                      FROM benchmark_membership GROUP BY benchmark_id) AS A INNER JOIN
                benchmarks ON A.benchmark_id = benchmarks.id;"""
      .query[BenchmarkMetadata]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t)      => prettyPrintException("Unable to get benchmark list", t)
      case Right(value) => value
    }
  }

  case class ProgramMetadata(name: String,
                             numPrograms: Int,
                             numPaths: Int,
                             numPerPath: Int)

  def getProgramList(conn: DBConnection): List[ProgramMetadata] = {
    sql"""SELECT programs.src_filename, A.num_programs, B.num_paths, C.num_per_Path
            FROM (SELECT program_id, COUNT(*) AS num_programs FROM permutations GROUP BY program_id) AS A
                INNER JOIN (SELECT program_id, COUNT(*) AS num_paths FROM paths GROUP BY program_id) AS B
                    ON A.program_id = B.program_id
                INNER JOIN (SELECT program_id, COUNT(*) AS num_per_Path FROM components GROUP BY program_id) AS C
                    ON B.program_id = C.program_id
                INNER JOIN programs ON programs.id = A.program_id;
       """
      .query[ProgramMetadata]
      .to[List]
      .transact(conn.xa)
      .attempt
      .unsafeRunSync() match {
      case Left(t) =>
        prettyPrintException("Unable to get list of program metadata", t)
      case Right(value) => value
    }
  }

  object Exporter {
    case class ProgramEntry(name: String, id: Long)

    case class BenchmarkEntry(name: String, id: Long)

    case class DynamicPerformanceEntry(programID: Long,
                                       permutationID: Long,
                                       measurementTypeID: Long,
                                       stress: Int,
                                       iter: Int,
                                       median: Double,
    ) {
      override def toString: String = {
        List(
          this.programID.toString,
          this.permutationID.toString,
          this.measurementTypeID.toString,
          this.stress.toString,
          this.iter.toString,
          this.median,
        ).mkString(",")
      }
    }

    def generateProgramIndex(c: DBConnection): String = {
      (for {
        l <- sql"""SELECT DISTINCT src_filename, programs.id
         FROM programs;"""
          .query[Exporter.ProgramEntry]
          .to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            "Unable to create mapping from program names to IDs",
            t)
        case Right(value) =>
          value
            .map(v => {
              List(v.name, v.id).mkString(",")
            })
            .mkString("\n")
      }
    }

    def generateProgramIndexFromPaths(paths: List[Long],
                                      c: DBConnection): String = {

      (for {
        _ <- generatePathIDTemporaryTable(paths)
        l <- sql"""SELECT DISTINCT src_filename, programs.id
               FROM programs CROSS JOIN paths p on programs.id = p.program_id
               WHERE p.id IN (SELECT path_id FROM requested_paths_ids);"""
          .query[Exporter.ProgramEntry]
          .to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            "Unable to create mapping from program names to IDs",
            t)
        case Right(value) =>
          value
            .map(v => {
              List(v.name, v.id).mkString(",")
            })
            .mkString("\n")
      }
    }

    def generateDynamicPerformanceData(stressTable: StressTable,
                                       paths: List[Long],
                                       c: DBConnection): String = {

      (for {
        _ <- Exporter.generatePathIDTemporaryTable(paths)
        _ <- Utilities.createTemporaryStressValueTable(stressTable)
        u <- sql"""
            SELECT A.program_id,
               A.permutation_id,
               A.measurement_type_id,
               A.stress,
               iter,
               median
        FROM (SELECT p.program_id, dp.permutation_id, dmt.id AS measurement_type_id, cs.stress, max(dp.last_updated), ANY_VALUE(dp.measurement_id) as mid
              FROM dynamic_performance dp
                       INNER JOIN permutations p on dp.permutation_id = p.id
                       CROSS JOIN steps on steps.permutation_id = dp.permutation_id
                       INNER JOIN dynamic_measurement_types dmt on dp.measurement_type_id = dmt.id
                       INNER JOIN programs p2 on p.program_id = p2.id
                       INNER JOIN configured_stress_values cs ON cs.program_id = p.program_id AND dp.stress = cs.stress
              GROUP BY p.program_id, dp.permutation_id, dmt.measurement_type, cs.stress) as A
                 INNER JOIN
             measurements ON measurements.id = A.mid;
             """.query[Exporter.DynamicPerformanceEntry].to[List]
      } yield u).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException("Unable to generate dynamic performance list", t)
        case Right(value) =>
          value
            .map(_.toString)
            .mkString("\n")
      }
    }

    def generateStaticPerformanceData(paths: List[Long],
                                      c: DBConnection): String = {

      case class StaticEntry(permID: Long, elim: Long, total: Long)

      (for {
        _ <- Exporter.generatePathIDTemporaryTable(paths)
        l <- sql"""SElECT DISTINCT s.permutation_id, sc.conj_eliminated, sc.conj_total FROM static_conjuncts sc
                    INNER JOIN permutations p on sc.permutation_id = p.id
                    INNER JOIN steps s on p.id = s.permutation_id
                    WHERE s.path_id IN (SELECT path_id FROM requested_paths_ids);
               """.query[StaticEntry].to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException("Unable to resolve static performance list", t)
        case Right(value) =>
          value
            .map(v => {
              List(v.permID, v.elim, v.total).mkString(",")
            })
            .mkString("\n")
      }
    }

    def generatePathIDTemporaryTable(
        paths: List[Long]): Free[connection.ConnectionOp, Int] = {
      for {
        _ <- sql"CREATE TEMPORARY TABLE requested_paths_ids (path_id BIGINT UNSIGNED NOT NULL);".update.run
        l <- Update[Long](
          "INSERT INTO requested_paths_ids (path_id) VALUES (?);")
          .updateMany(paths)
      } yield l
    }

    def generatePathIndex(paths: List[Long], c: DBConnection): String = {
      case class IndexRow(programID: Long,
                          permID: Long,
                          pathID: Long,
                          levelID: Long)

      (for {
        _ <- Exporter.generatePathIDTemporaryTable(paths)
        l <- sql"""SELECT * FROM path_step_index WHERE path_id IN (SELECT path_id FROM requested_paths_ids);"""
          .query[IndexRow]
          .to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) => prettyPrintException("Unable to resolve path index", t)
        case Right(value) =>
          value
            .map(r =>
              List(r.programID, r.permID, r.pathID, r.levelID).mkString(","))
            .mkString("\n")
      }
    }

    def generateMeasurementTypeIndex(c: DBConnection): String = {
      case class IndexRow(mtID: Long, mt: String)

      (for {
        l <- sql"""SELECT * FROM dynamic_measurement_types;"""
          .query[IndexRow]
          .to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) => prettyPrintException("Unable to resolve path index", t)
        case Right(value) =>
          value
            .map(r => List(r.mtID, r.mt).mkString(","))
            .mkString("\n")
      }
    }

    def getPathIDList(vid: Long,
                      hid: Long,
                      table: StressTable,
                      c: DBConnection): Map[Long, List[Long]] = {
      case class CompletedPathID(programID: Long, pathID: Long)

      (for {
        _ <- Utilities.createTemporaryStressValueTable(table)
        v <- sql"""SELECT DISTINCT completed_paths.program_id, completed_paths.path_id
        FROM completed_paths
                 INNER JOIN
             (SELECT path_id, COUNT(DISTINCT measurement_type_id) AS mcount, COUNT(DISTINCT cs.stress) AS ccount
              FROM completed_paths cp
                       CROSS JOIN configured_stress_values cs
                           ON cs.program_id = cp.program_id AND cp.stress = cs.stress
              GROUP BY path_id)
                 AS stress_counts ON completed_paths.path_id = stress_counts.path_id
                 INNER JOIN configured_stress_counts
            AS target_counts ON target_counts.program_id = completed_paths.program_id
        WHERE version_id = $vid
          AND hardware_id = $hid
          AND stress_counts.ccount = target_counts.stress_count
          AND stress_counts.mcount = (SELECT COUNT(*) FROM dynamic_measurement_types);"""
          .query[CompletedPathID]
          .to[List]
      } yield v).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            "Unable to resolve list of completed paths matching criteria",
            t)
        case Right(value) =>
          value.groupBy(_.programID).map(g => g._1 -> g._2.map(_.pathID))
      }
    }

    def getBenchmarkIDList(vid: Long,
                           hid: Long,
                           table: StressTable,
                           c: DBConnection): List[BenchmarkEntry] = {

      (for {
        _ <- Utilities.createTemporaryStressValueTable(table)
        v <- sql"""SELECT DISTINCT benchmark_name, completed_benchmarks.benchmark_id
        FROM completed_benchmarks
                 INNER JOIN benchmarks
                            ON completed_benchmarks.benchmark_id = benchmarks.id
                 INNER JOIN (SELECT hardware_id,
                                    version_id,
                                    cb.benchmark_id,
                                    COUNT(DISTINCT measurement_type_id) AS mcount,
                                    COUNT(DISTINCT cs.stress)           AS scount

                             FROM completed_benchmarks cb
                                 INNER JOIN benchmark_membership ON cb.benchmark_id = benchmark_membership.benchmark_id
                                 INNER JOIN permutations p on benchmark_membership.permutation_id = p.id
                                      CROSS JOIN configured_stress_values cs
                                                 ON cb.stress = cs.stress
                                                    AND p.program_id = cs.program_id
                             GROUP BY hardware_id, version_id, cb.benchmark_id) as ct
                            ON ct.version_id = completed_benchmarks.version_id
                                AND ct.hardware_id = completed_benchmarks.hardware_id
                                AND ct.benchmark_id = completed_benchmarks.benchmark_id
        WHERE completed_benchmarks.version_id = $vid
          AND completed_benchmarks.hardware_id = $hid
          AND ct.scount = (SELECT SUM(DISTINCT stress_count) FROM configured_stress_counts)
          AND ct.mcount = (SELECT COUNT(*) FROM dynamic_measurement_types);"""
          .query[Exporter.BenchmarkEntry]
          .to[List]
      } yield v).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException("Unable to resolve list of completed benchmarks",
                               t)
        case Right(value) => value
      }
    }

    def getBenchmarkPerformanceData(stressTable: StressTable,
                                    id: Long,
                                    c: DBConnection): String = {

      (for {
        _ <- Utilities.createTemporaryStressValueTable(stressTable)
        l <- sql"""SELECT p.program_id, dp.permutation_id, dmt.measurement_type, cs.stress,
                      iter, ninety_fifth, fifth, median, mean, stdev, minimum, maximum
                    FROM benchmark_membership
                    INNER JOIN permutations p ON benchmark_membership.permutation_id = p.id
                    CROSS JOIN dynamic_performance dp ON p.id = dp.permutation_id
                    INNER JOIN configured_stress_values cs
                        ON dp.stress = cs.stress AND cs.program_id = p.program_id
                    INNER JOIN dynamic_measurement_types dmt on dp.measurement_type_id = dmt.id
                    INNER JOIN measurements m on dp.measurement_id = m.id;
             """.query[Exporter.DynamicPerformanceEntry].to[List]
      } yield l).transact(c.xa).attempt.unsafeRunSync() match {
        case Left(t) =>
          prettyPrintException(
            s"Unable to acquire dynamic peformance results for benchmark ID=$id",
            t)
        case Right(value) =>
          value.map(_.toString).mkString("\n")
      }
    }
  }

  object Utilities {
    def createTemporaryStressValueTable(
        stressTable: StressTable): Free[connection.ConnectionOp, Int] = {
      case class ProgramEntry(filename: String, programID: Long)
      case class ProgramStressEntry(programID: Long, stress: Int)

      for {
        e <- sql"SELECT src_filename, id FROM programs;"
          .query[ProgramEntry]
          .to[List]
        _ <- sql"CREATE TEMPORARY TABLE configured_stress_values (program_id BIGINT UNSIGNED NOT NULL, stress INT UNSIGNED NOT NULL);".update.run
        u <- Update[ProgramStressEntry](
          "INSERT INTO configured_stress_values (program_id, stress) VALUES (?, ?);")
          .updateMany(
            e.map(e => e.filename -> e.programID)
              .toMap
              .flatMap(p => {
                for {
                  w <- stressTable.get(p._1)
                } yield ProgramStressEntry(p._2, w)
              })
              .toList)
        _ <- sql"""CREATE temporary table configured_stress_counts
          (
            program_id BIGINT UNSIGNED,
            stress_count BIGINT UNSIGNED
          );""".update.run
        u <- sql"""INSERT INTO configured_stress_counts
                    SELECT program_id, COUNT(*) AS c
                        FROM configured_stress_values cs
                        GROUP BY program_id;""".update.run
      } yield u
    }
  }
}
