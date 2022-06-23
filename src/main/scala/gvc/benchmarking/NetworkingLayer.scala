package gvc.benchmarking
import gvc.benchmarking.NetworkingUtilities.{
  ClientIdentification,
  Message,
  parseMessage
}
import java.io.{
  DataInputStream,
  DataOutputStream,
  IOException,
  ObjectOutputStream
}
import java.net.{ServerSocket, Socket}
import java.nio.ByteBuffer
import java.util.concurrent.{Executors, LinkedBlockingQueue}
case class NetworkConfig(port: Int)

object NetworkingUtilities {
  case class Message(jobID: Int, serializedContents: Array[Byte])

  case class ClientIdentification(verifierID: String, hardwareID: String)
      extends Serializable

  def parseMessage(bytes: Array[Byte]): Option[Message] = {
    val jobID = ByteBuffer.wrap(bytes.slice(0, 4)).getInt
    Some(Message(jobID, bytes.slice(4, bytes.length)))
  }
}

class ClientNetworkingLayer(
    port: Int,
    host: String,
    hostPort: Int,
    handleJob: (Message) => Unit,
    id: ClientIdentification
) extends Thread {
  private val connection = new Socket(host, hostPort)
  override def run(): Unit = {
    val oos = new ObjectOutputStream(connection.getOutputStream)
    oos.writeObject(id)
    oos.flush()
    try {
      while (true) {
        val dis = new DataInputStream(connection.getInputStream)
        val jobRequest = dis.readAllBytes()
        val parsedJob = parseMessage(jobRequest)
        parsedJob match {
          case Some(value) => handleJob(value)
          case None        =>
        }
      }
    }
  }
  // TODO: extract from fnc to not have to call `sendResult` in `BenchmarkServer.scala`
  def sendResult(res: Message): Unit = {
    val os = new DataOutputStream(connection.getOutputStream)
    val concatenated =
      BigInt.int2bigInt(res.jobID).toByteArray ++ res.serializedContents
    os.write(concatenated)
    os.flush()
  }
}

class ServerNetworkingLayer(
    port: Int,
    threads: Int = 8,
    onCompletion: Message => Unit,
    onFailure: Message => Unit
) extends Thread {
  private val serverSocket = new ServerSocket(port)
  private val pool = Executors.newFixedThreadPool(threads)
  private val msgQueue = new LinkedBlockingQueue[Message]()
  override def run(): Unit = {
    try {
      while (true) {
        pool.execute(
          new MessageHandlerThread(
            serverSocket.accept(),
            onCompletion,
            onFailure
          )
        )
      }
    } catch {
      case _: IOException => close()
      case _: InterruptedException =>
        pool.shutdownNow
        Thread.currentThread.interrupt()
    }
  }
  def delegate(msg: Message): Unit = {
    msgQueue.add(msg)
  }

  def close(): Unit = {
    import java.util.concurrent.TimeUnit
    pool.shutdown() // Disable new tasks from being submitted
    try // Wait a while for existing tasks to terminate
      if (!pool.awaitTermination(60, TimeUnit.SECONDS)) {
      pool.shutdownNow // Cancel currently executing tasks

      // Wait a while for tasks to respond to being cancelled
      if (!pool.awaitTermination(60, TimeUnit.SECONDS))
        System.err.println("Pool did not terminate")
    } catch {
      case _: InterruptedException =>
        // (Re-)Cancel if current thread also interrupted
        pool.shutdownNow
        // Preserve interrupt status
        Thread.currentThread.interrupt()
    }
  }

  class MessageHandlerThread(
      socket: Socket,
      onCompletion: Message => Unit,
      onFailure: Message => Unit
  ) extends Thread {
    override def run(): Unit = {
      while (!this.isInterrupted) {
        val msg = msgQueue.poll()
        val os = new DataOutputStream(socket.getOutputStream)
        val concatenated =
          BigInt.int2bigInt(msg.jobID).toByteArray ++ msg.serializedContents
        os.write(concatenated)
        os.flush()

        val is = new DataInputStream(socket.getInputStream)
        val readResult = is.readAllBytes()

        val parsedMessage = parseMessage(readResult)
        parsedMessage match {
          case Some(read) => onCompletion(read)
          case None       =>
        }
      }
    }
  }
}
