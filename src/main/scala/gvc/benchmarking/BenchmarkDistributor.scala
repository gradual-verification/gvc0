package gvc.benchmarking

import gvc.CC0Wrapper.Performance
import gvc.benchmarking.BenchmarkRequest.{TaskRequest, TerminationRequest}
import gvc.benchmarking.BenchmarkResult.DistributorSignature
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.ErrorType.ErrorType
import gvc.benchmarking.DAO.{
  DBConnection,
  Identity,
  releaseReservedPermutations
}

import scala.collection.JavaConverters._
import upickle.default
import upickle.default._

import java.io.{DataInputStream, DataOutputStream, IOException}
import java.net.{ServerSocket, Socket}
import java.util.concurrent.{ConcurrentHashMap, LinkedBlockingQueue}
import scala.collection.mutable

sealed trait BenchmarkRequest

object BenchmarkRequest {
  implicit val readWriter: ReadWriter[BenchmarkRequest] = ReadWriter.merge(
    macroRW[TaskRequest],
    macroRW[TerminationRequest]
  )

  case class TaskRequest(md5: String,
                         permutationID: Long,
                         permutation: Array[Byte],
                         workloads: List[Int],
                         mode: DynamicMeasurementMode)
      extends BenchmarkRequest

  case class TerminationRequest() extends BenchmarkRequest
}

case class TaggedResult(result: BenchmarkResult,
                        id: Identity,
                        permutationID: Long)

sealed trait BenchmarkResult

object BenchmarkResult {

  import upickle.default._

  implicit val readWriter: ReadWriter[BenchmarkResult] = ReadWriter.merge(
    macroRW[StaticFailure],
    macroRW[DynamicResults]
  )

  case class StaticFailure(error: BenchmarkError) extends BenchmarkResult

  case class DistributorSignature(id: Identity, execSig: ExecutorSignature)

  case class DynamicResults(failures: Map[Int, BenchmarkError],
                            successes: Map[Int, Performance])
      extends BenchmarkResult
}

case class BenchmarkError(message: String, errorType: ErrorType)

object BenchmarkError {
  implicit val rw: default.ReadWriter[BenchmarkError] =
    macroRW[BenchmarkError]
}

class BenchmarkDistributor(config: DistributorConfig) {

  private val conn: DBConnection = DAO.connect(config.db)

  Output.info(s"Starting distribution server on port: ${config.queue.port}")
  private val server = new ServerSocket(config.queue.port)

  private val synchronizedMap =
    new ConcurrentHashMap[DistributorSignature,
                          LinkedBlockingQueue[BenchmarkRequest]]()
  private val connectedClients =
    new ConcurrentHashMap[DistributorSignature, Unit]()

  private val resultsQueue = new LinkedBlockingQueue[Option[TaggedResult]]()

  def distribute(): Unit = {
    Output.info("Starting job queue population.")
    new Thread(new BenchmarkProducer(config.queue)).start()
    Output.info("Starting result queue consumption.")
    new Thread(new BenchmarkConsumer()).start()
    Output.info("Accepting clients...")
    while (true) {
      val clientSocket = server.accept()
      new Thread(new BenchmarkRunner(clientSocket)).start()
    }
  }

  private class BenchmarkRunner(socket: Socket) extends Runnable {

    val queue = new LinkedBlockingQueue[BenchmarkRequest]()
    private var workRemains = false

    def run(): Unit = {
      try {
        socket.setKeepAlive(true)
        val is = new DataInputStream(socket.getInputStream)
        val os = new DataOutputStream(socket.getOutputStream)
        val signature = read[ExecutorSignature](is.readUTF())
        val resolvedID = DAO.addOrResolveIdentity(signature, conn)
        val distribSignature = DistributorSignature(resolvedID, signature)
        synchronizedMap.put(distribSignature, this.queue)
        connectedClients.put(distribSignature, Unit)
        Output.success(
          s"Accepted connection from client: ${signature.toString}@${socket.getInetAddress.getHostAddress}")
        while (socket.isConnected && workRemains) {
          val request = this.queue.take()
          request match {
            case task: TaskRequest =>
              val serializedRequest =
                write[Option[BenchmarkRequest]](Some(task))
              os.writeUTF(serializedRequest)
              val serializedResult = is.readUTF()
              val readResult = read[BenchmarkResult](serializedResult)
              resultsQueue.put(
                Some(TaggedResult(readResult, resolvedID, task.permutationID)))
            case _: TerminationRequest =>
              Output.success("")
              Output.info(
                s"All requested jobs completed, sending termination indicator to client ${signature.toString}")
              val serializedRequest = write[Option[BenchmarkRequest]](None)
              os.writeUTF(serializedRequest)
              workRemains = false
          }
        }
        os.flush()
        os.close()
        is.close()
        socket.close()
      } catch {
        case _: IOException =>
          Output.error(
            s"Lost connection to client ${socket.getInetAddress.getHostAddress}")
      }
    }
  }

  private class BenchmarkProducer(config: BenchmarkQueueConfig)
      extends Runnable {
    def run(): Unit = {
      while (true) {
        synchronizedMap.synchronized {
          val toRemove = mutable.ListBuffer[DistributorSignature]()
          synchronizedMap.keySet.forEach(k => {
            if (connectedClients.contains(k)) {
              val queue = synchronizedMap.get(k)
              if (queue.size() < config.queueLength) {
                val differenceToRepopulate = config.queueLength - queue.size()
                val reservedTasks =
                  DAO.reservePermutations(k, differenceToRepopulate, conn)
                queue.addAll(reservedTasks.asJavaCollection)
                if (reservedTasks.size < differenceToRepopulate) {
                  queue.put(TerminationRequest())
                }
              }
            } else {
              releaseReservedPermutations(k, conn)
              toRemove += k
            }
          })
          toRemove.foreach(synchronizedMap.remove)
        }
        Thread.sleep(config.repopulationDelay)
      }
    }
  }

  private class BenchmarkConsumer() extends Runnable {
    private var resultsRemaining = true

    def run(): Unit = {
      while (resultsRemaining) {
        val result = resultsQueue.take()
        result match {
          case Some(r) =>
            DAO.processTaggedResult(r)
          case None => resultsRemaining = false
        }
      }
    }
  }
}
