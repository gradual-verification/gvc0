package gvteal.specs

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest._

object BaseFileSpec {
  private var UPDATE: Option[Boolean] = None
  private var CLASSPATH: Option[String] = None

  private def init(config: ConfigMap): Unit = {
    if (UPDATE == None)
      UPDATE = Some(config.contains("update_files"))
    if (CLASSPATH == None)
      CLASSPATH = Some(config("classpath").toString())
  }
}

trait BaseFileSpec extends BeforeAndAfterAllConfigMap {
  this: AnyFunSuite =>
  
  override protected def beforeAll(configMap: ConfigMap): Unit = {
    BaseFileSpec.init(configMap)
  }

  def getClasspath = BaseFileSpec.CLASSPATH.get

  def assertFile(resource: TestResource, actual: String): Unit = {
    if (BaseFileSpec.UPDATE.get) {
      if (actual != resource.read())
        resource.update(actual)
    } else {
      assert(actual == resource.read())
    }
  }

  def assertFile(resource: Option[TestResource], actual: String): Unit = {
    resource.foreach(assertFile(_, actual))
  }
}