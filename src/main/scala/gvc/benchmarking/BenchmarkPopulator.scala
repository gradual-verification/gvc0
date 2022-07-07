package gvc.benchmarking

import gvc.{Config, Main}

import java.net.{JarURLConnection, URL}
import java.nio.file.{Files, Path}

class BenchmarkPopulator {
  private val BASELINE_QUANTITY = 1024

  def generateBenchmarks(sourceDir: Path): Unit = {}

  def syncProgram(filename: Path, config: Config): Unit = {
    val sourceText = Files.readString(filename)
    val sourceIR = Main.generateIR(sourceText, List())
    val labels = new LabelVisitor().visit(sourceIR)

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
