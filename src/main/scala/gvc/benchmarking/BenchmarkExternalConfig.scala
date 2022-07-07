package gvc.benchmarking

import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.sys.exit
import scala.xml.{Elem, XML}

class BenchmarkExternalConfig {

  class BenchmarkConfigException(message: String) extends Exception(message)

  case class BenchmarkConfig(
      platformIdentification: Option[PlatformIdentification],
      workload: BenchmarkWorkload,
      input: BenchmarkIO
  )

  case class BenchmarkIO(
      outputDir: Path,
      input: List[Path]
  )

  case class BenchmarkWorkload(
      iterations: Int,
      nPaths: Int,
      stress: Stress
  )

  trait Stress

  case class StressBounded(wUpper: Int, wStep: Int) extends Stress

  case class StressList(wList: List[Int]) extends Stress

  case class StressSingular(stressValue: Int) extends Stress

  case class PlatformIdentification(versionID: String, hardwareID: String)

  def parse(xmlInput: Path): BenchmarkConfig = {
    val xml = XML.loadFile(xmlInput.toFile)
    try {
      val id = parseID(xml)
      val io = parseIO(xml)
      val workload = parseWorkload(xml)
      BenchmarkConfig(
        id,
        workload,
        io,
      )
    } catch {
      case benchmarkConfigException: BenchmarkConfigException =>
        Output.error(benchmarkConfigException.toString)
        exit(1)
    }
  }

  def parseID(xml: Elem): Option[PlatformIdentification] = {
    val idRoot = xml \\ "id"
    if (idRoot.isEmpty) {
      None
    } else {
      val versionID = idRoot \ "version"
      val hardwareID = idRoot \ "hardware"
      if (versionID.isEmpty) {
        throw new BenchmarkConfigException("Missing <id> field <version>")
      } else if (hardwareID.isEmpty) {
        throw new BenchmarkConfigException("Missing <id> field <hardware>")
      } else {
        Some(PlatformIdentification(versionID.text, hardwareID.text))
      }
    }
  }

  def parseIO(xml: Elem): BenchmarkIO = {
    val ioRoot = xml \\ "io"
    if (ioRoot.isEmpty) {
      throw new BenchmarkConfigException("Missing <io> configuration")
    } else {
      val sources = ioRoot \ "sources"
      val source = ioRoot \ "source"
      val output = ioRoot \ "output"
      if (output.isEmpty) {
        throw new BenchmarkConfigException("Missing <io> field <output>")
      } else {
        val outputDir = Paths.get(output.text)
        val sourceList = mutable.ListBuffer[Path]()
        if (sources.nonEmpty) {
          val sourceDir = Paths.get(sources.text)
          if (Files.isDirectory(sourceDir)) {
            sourceList ++= sourceDir.toFile.listFiles
              .filter(_.isFile)
              .toList
              .map(_.toPath)
          } else {
            throw new BenchmarkConfigException(
              s"Expected a directory for <sources> field, but was provided a regular file: ${sourceDir.toString}")
          }
        }
        if (source.nonEmpty) {
          val singleSourcePath = Paths.get(source.text)
          if (!Files.exists(singleSourcePath) || !Files.isRegularFile(
                singleSourcePath)) {
            throw new BenchmarkConfigException(
              s"The specified <source> file is invalid: ${source.text}")
          } else {
            sourceList += singleSourcePath
          }
        }
        if (sourceList.isEmpty) {
          throw new BenchmarkConfigException(
            "A single <source> or multiple <sources> must be specified.")
        } else {
          BenchmarkIO(
            outputDir,
            sourceList.toList
          )
        }
      }
    }
  }

  def parseWorkload(xml: Elem): BenchmarkWorkload = {
    BenchmarkWorkload(1, 1, parseStress(xml))
  }

  def parseStress(xml: Elem): Stress = {
    StressSingular(1)
  }
}
