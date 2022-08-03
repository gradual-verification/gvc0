package gvc.benchmarking

import gvc.CC0Wrapper.Performance
import gvc.benchmarking.DAO.DynamicMeasurementMode.DynamicMeasurementMode
import gvc.benchmarking.DAO.ErrorType.ErrorType
import upickle.default
import upickle.default._

import java.io.{DataInputStream, DataOutputStream, IOException}
import java.net.{ServerSocket, Socket}
import java.util.concurrent.{ConcurrentHashMap, LinkedBlockingQueue}

sealed trait BenchmarkRequest;
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

sealed trait BenchmarkResult
object BenchmarkResult {
  import upickle.default._
  implicit val readWriter: ReadWriter[BenchmarkResult] = ReadWriter.merge(
    macroRW[StaticFailure],
    macroRW[DynamicResults]
  )
  case class StaticFailure(error: BenchmarkError) extends BenchmarkResult
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

  Output.info(s"Starting distribution server on port: ${config.queue.port}")
  val server = new ServerSocket(config.queue.port)

  val synchronizedMap =
    new ConcurrentHashMap[ExecutorSignature,
                          LinkedBlockingQueue[Option[BenchmarkRequest]]]()
  val connectedClients =
    new ConcurrentHashMap[ExecutorSignature, Unit]()

  val resultsQueue = new LinkedBlockingQueue[Option[BenchmarkResult]]()

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

  class BenchmarkRunner(socket: Socket) extends Runnable {

    val queue = new LinkedBlockingQueue[Option[BenchmarkRequest]]()
    private var workRemains = false

    def run(): Unit = {
      try {
        socket.setKeepAlive(true)
        val is = new DataInputStream(socket.getInputStream)
        val os = new DataOutputStream(socket.getOutputStream)
        val signature = read[ExecutorSignature](is.readUTF())
        synchronizedMap.put(signature, this.queue)
        connectedClients.put(signature, Unit)
        Output.success(
          s"Accepted connection from client: ${signature.toString}@${socket.getInetAddress.getHostAddress}")
        while (socket.isConnected && workRemains) {
          val request = this.queue.take()
          request match {
            case Some(value) =>
              val serializedRequest =
                write[Option[BenchmarkRequest]](Some(value))
              os.writeUTF(serializedRequest)
              val serializedResult = is.readUTF()
              val readResult = read[BenchmarkResult](serializedResult)
              resultsQueue.put(Some(readResult))
            case None =>
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

  class BenchmarkProducer(config: BenchmarkQueueConfig) extends Runnable {
    def run(): Unit = {
      while (true) {
        synchronizedMap.synchronized {}
        Thread.sleep(config.repopulationDelay)
      }
    }
  }

  class BenchmarkConsumer() extends Runnable {
    private var resultsRemain = true

    def run(): Unit = {
      while (resultsRemain) {
        val result = resultsQueue.take()
        result match {
          case Some(_) =>
          case None    => resultsRemain = false
        }
      }
    }
  }
}
