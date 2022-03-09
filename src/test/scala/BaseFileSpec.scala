package gvc.specs

import scala.io.Source
import java.io.{File, PrintWriter}
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.BeforeAndAfterAllConfigMap
import org.scalatest.ConfigMap

trait BaseFileSpec extends BeforeAndAfterAllConfigMap {
  this: AnyFunSuite =>
  var UPDATE = false
  
  override protected def beforeAll(configMap: ConfigMap): Unit = {
    UPDATE = configMap.contains("update_files")
  }

  def getFiles(dir: String):List[String] = {
    val base =  new File(getClass().getResource("/" + dir).getFile())
    val contents = base.listFiles()
    if(contents != null) {
      contents.map(f => dir + "/" + f.getName()).toList
    }else{
      List()
    }
  }

  def getFile(name: String): Option[String] = getClass().getResource("/" + name) match {
    case null => None
    case url => Some(Source.fromURL(url).mkString)
  }

  def assertFile(name: String, actual: String): Unit = {
    getFile(name).foreach { expected =>
      if (UPDATE) {
        if (actual != expected)
          writeFile(name, actual)
      } else {
        assert(actual == expected)
      }
    }
  }

  def writeFile(name: String, value: String): Unit = {
    val path = "src/test/resources/" + name
    new PrintWriter(new File(path)) {
      write(value)
      close()
    }
  }
}