package gvc.benchmarking

import gvc.Main

import java.nio.file.Path

class CC[T] { def unapply(a: Any): Option[T] = Some(a.asInstanceOf[T]) }

object M extends CC[Map[String, Any]]
object L extends CC[List[Any]]
object S extends CC[String]
object D extends CC[Double]
object B extends CC[Boolean]

object ExternalConfig {

  def createFromJSON(configPath: Path): Unit = {
    val contents = Main.readFile(configPath.toFile.toString)

  }
}
