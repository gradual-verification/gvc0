package gvc.benchmarking

import gvc.{Config, Main}
import java.net.{JarURLConnection, URL}
import java.nio.file.Files

object BenchmarkPopulator {
  private val BASELINE_QUANTITY = 1024

  //https://alvinalexander.com/source-code/scala-method-create-md5-hash-of-string/
  private def md5sum(contents: String): String = {
    import java.math.BigInteger
    import java.security.MessageDigest
    val md = MessageDigest.getInstance("MD5")
    val digest: Array[Byte] = md.digest(contents.getBytes)
    val bigInt = new BigInteger(1, digest)
    val hashedPassword = bigInt.toString(16).trim
    prependWithZeros(hashedPassword)
  }

  private def prependWithZeros(pwd: String): String =
    "%1$32s".format(pwd).replace(' ', '0')

  def populate(populatorConfig: PopulatorConfig): Unit = {}

  def syncProgram(filename: java.nio.file.Path, config: Config): Unit = {
    val sourceText = Files.readString(filename)
    val sourceIR = Main.generateIR(sourceText, List())
    val labels = new LabelVisitor().visit(sourceIR)
    //val insertedProgram =
    //Queries.addOrResolveProgram(filename,
    //                            md5sum(sourceText),
    //                            labels.labels.size)
  }

  //https://stackoverflow.com/questions/38204059/how-to-obtain-a-package-version-from-the-jars-manifest-using-the-getimplementa
  def getVersionID(): Option[String] = {
    val className = getClass.getSimpleName + ".class"
    val classPath = getClass.getResource(className).toString
    if (!classPath.startsWith("jar")) return None
    val url = new URL(classPath)
    val jarConnection = url.openConnection.asInstanceOf[JarURLConnection]
    val manifest = jarConnection.getManifest
    val attributes = manifest.getMainAttributes
    Some(attributes.getValue("Implementation-Version"))
  }

}
