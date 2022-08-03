package gvc.pbt

import gvc.{Config}
import gvc.Config.error
import java.nio.file.{Files, InvalidPathException, Path, Paths}
import scala.xml.{NodeSeq, XML}

class InputGeneratorException(message: String) extends Exception(message)

object InputGeneratorConfig {

//  private object Names {
//    val defaultOutputDirectory = "./data"
//  }
//
//  def parseMonitor(rootConfig: Config): MonitorConfig = {
//    val resolved = parseConfig(rootConfig)
//    MonitorConfig(
//      resolved.credentials,
//      Paths.get(resolved.outputDir.getOrElse(Names.defaultOutputDirectory))
//    )
//  }
//
//  def parseRecreator(rootConfig: Config): RecreatorConfig = {
//    val resolved = parseConfig(rootConfig)
//    rootConfig.recreatePerm match {
//      case Some(value) =>
//        RecreatorConfig(resolved.version,
//                        resolved.credentials,
//                        resolved.sources,
//                        value)
//      case None => error("Expected an integer value passed to --recreate.")
//    }
//  }
//
//  def parseExecutor(rootConfig: Config): ExecutorConfig = {
//    val resolved = parseConfig(rootConfig)
//    resolved.workload match {
//      case Some(wValue) =>
//        resolved.hardware match {
//          case Some(hValue) =>
//            ExecutorConfig(
//              resolved.version,
//              hValue,
//              resolved.nickname,
//              resolved.credentials,
//              resolved.sources,
//              wValue
//            )
//          case None => error("A <hardware> must be provided.")
//        }
//
//      case None => error("A <workload> must be provided.")
//    }
//  }
//
//  def parsePopulator(rootConfig: Config): PopulatorConfig = {
//    val resolved = parseConfig(rootConfig)
//    PopulatorConfig(resolved.version,
//                    resolved.pathQuantity,
//                    resolved.credentials,
//                    resolved.sources)
//  }
//
//  private def parseConfig(rootConfig: Config): BenchmarkConfigResults = {
//    val configPath = rootConfig.config.get
//    val xml = XML.loadFile(configPath.toFile)
//    val benchmarkRoot = xml \\ "benchmark"
//    if (benchmarkRoot.isEmpty) {
//      error("Expected <benchmark> element.")
//    } else {
//      val version =
//        resolveFallback("version", benchmarkRoot, rootConfig.versionString)
//      val hardware =
//        resolveFallbackOptional("hardware",
//                                benchmarkRoot,
//                                rootConfig.hardwareString)
//      val nickname =
//        resolveFallbackOptional("nickname",
//                                benchmarkRoot,
//                                rootConfig.nicknameString)
//      val quantity =
//        intOption(benchmarkRoot \ "quantity")
//
//      val sourceDirElement = benchmarkRoot \ "source-dir"
//      if (sourceDirElement.isEmpty || sourceDirElement.text.trim.isEmpty) {
//        error("Expected <source-dir> field.")
//      }
//      val sourceDirText = sourceDirElement.text
//      val sourceDirPath = validateDirectory(sourceDirText, "source-dir")
//      val c0SourceFiles = sourceDirPath.toFile
//        .listFiles()
//        .filter(_.isFile)
//        .toList
//        .filter(p => {
//          p.getName.endsWith(".c0")
//        })
//        .map(_.toPath)
//      val fileCollection = rootConfig.sourceFile match {
//        case Some(value) => c0SourceFiles ++ List(Paths.get(value))
//        case None        => c0SourceFiles
//      }
//
//      val outputDir = (benchmarkRoot \ "output-dir")
//      val outputDirText =
//        if (outputDir.isEmpty || outputDir.text.trim.isEmpty) None
//        else Some(outputDir.text.trim)
//
//      val credentials = parseDB(benchmarkRoot \\ "db", rootConfig)
//
//      val workload = parseWorkload(benchmarkRoot \\ "workload")
//
//      val modifiers = parsePipelineModifiers(benchmarkRoot)
//
//      BenchmarkConfigResults(version,
//                             hardware,
//                             nickname,
//                             credentials,
//                             fileCollection,
//                             workload,
//                             quantity,
//                             modifiers,
//                             outputDirText)
//    }
//  }
//
//  def generateStressList(stress: StressConfiguration): List[Int] = {
//    val stepList = stress match {
//      case singular: StressSingular => List(singular.stressValue)
//      case list: StressList         => list.wList
//      case stepwise: StressBounded =>
//        (stepwise.wLower to stepwise.wUpper by stepwise.wStep).toList
//    }
//    stepList
//  }
//
//  private def resolveFallback(field: String,
//                              xml: NodeSeq,
//                              fallback: Option[String]) = {
//    fallback match {
//      case Some(value) => value
//      case None => {
//        val provided = xml \ field
//        if (provided.nonEmpty) {
//          provided.text.trim
//
//        } else {
//          error(
//            s"No $field string has been provided, either as a command line argument (--$field) or configuration file field.")
//        }
//      }
//    }
//  }
//
//  private def resolveFallbackOptional(field: String,
//                                      xml: NodeSeq,
//                                      fallback: Option[String]) = {
//    fallback match {
//      case Some(_) => fallback
//      case None =>
//        val provided = xml \ field
//        if (provided.nonEmpty) {
//          Some(provided.text.trim)
//
//        } else {
//          None
//        }
//    }
//  }
//
//  private def parsePipelineModifiers(xml: NodeSeq): PipelineModifiers = {
//    PipelineModifiers(
//      onlyVerify = false,
//      onlyCompile = false,
//      disableBaseline = false
//    )
//  }
//
//  private def parseDB(xml: NodeSeq,
//                      rootConfig: Config): BenchmarkDBCredentials = {
//    val url = resolveFallback("url", xml, rootConfig.dbURLString)
//    val username = resolveFallback("username", xml, rootConfig.dbUserString)
//    val password = resolveFallback("password", xml, rootConfig.dbPassString)
//    BenchmarkDBCredentials(
//      url,
//      username,
//      password,
//    )
//  }
//
//  private def intOrError(xml: NodeSeq, errorText: String): Int = {
//    try {
//      xml.text.toInt
//    } catch {
//      case _: NumberFormatException =>
//        error(errorText)
//    }
//  }
//
//  private def intOption(xml: NodeSeq): Option[Int] = {
//    try {
//      Some(xml.text.toInt)
//    } catch {
//      case _: NumberFormatException =>
//        None
//    }
//  }
//
//  private def validateDirectory(pathText: String,
//                                tag: String): java.nio.file.Path = {
//    try {
//      val converted = Paths.get(pathText)
//      if (Files.exists(converted)) {
//        if (Files.isDirectory(converted)) {
//          converted
//        } else {
//          error(
//            s"<$tag>: Expected a directory but found a regular file: $pathText")
//        }
//      } else {
//        error(s"<$tag>: The specified directory $pathText doesn't exist.")
//      }
//    } catch {
//      case _: InvalidPathException => {}
//      error(s"<$tag>: Invalid path format: $pathText")
//    }
//  }
//
//  private def validateFile(pathText: String,
//                           tag: String): java.nio.file.Path = {
//    try {
//      val converted = Paths.get(pathText)
//      if (Files.exists(converted)) {
//        if (Files.isRegularFile(converted)) {
//          converted
//        } else {
//          error(s"<$tag>: Expected a file but found a directory: $pathText")
//        }
//      } else {
//        error(s"<$tag>: The specified file $pathText doesn't exist.")
//      }
//    } catch {
//      case _: InvalidPathException => {}
//      error(s"<$tag>: Invalid path format: $pathText")
//    }
//  }
//
//  private def parseWorkload(xml: NodeSeq): Option[BenchmarkWorkload] = {
//    val workloadRoot = xml \\ "workload"
//    if (workloadRoot.isEmpty) {
//      None
//    } else {
//      val paths = workloadRoot \ "paths"
//      val iterations = workloadRoot \ "iterations"
//      val staticIterations = workloadRoot \ "static-iterations"
//      val iterQuantity =
//        if (iterations.isEmpty) 1
//        else
//          intOrError(
//            iterations,
//            s"Expected an integer for <iterations>, but found: '${iterations.text}")
//      val staticIterQuantity =
//        if (staticIterations.isEmpty) 1
//        else
//          intOrError(
//            staticIterations,
//            s"Expected an integer for <static-iterations>, but found: '${staticIterations.text}")
//      val pathQuantity =
//        if (paths.isEmpty) 1
//        else
//          intOrError(
//            paths,
//            s"Expected an integer for <paths>, but found: '${paths.text}'")
//      val stress = workloadRoot \\ "stress"
//      Some(
//        BenchmarkWorkload(iterQuantity,
//                          staticIterQuantity,
//                          pathQuantity,
//                          parseStress(stress)))
//    }
//  }
//
//  private def parseStress(xml: NodeSeq): StressConfiguration = {
//    val listed = parseStressListed(xml \ "list")
//    val singular = parseStressSingular(xml \ "singular")
//    val bounded = parseStressBounded(xml \ "bounded")
//
//    val specified = List(listed, singular, bounded).filter(_.nonEmpty)
//    if (specified.length > 1) {
//      error(
//        "Only one workload specification method can be used for <stress>; multiple were found.")
//    } else {
//      specified.head match {
//        case Some(value) => value
//        case None =>
//          error("Missing workload specification under <stress>")
//      }
//    }
//  }
//
//  private def parseStressBounded(xml: NodeSeq): Option[StressConfiguration] = {
//    if (xml.isEmpty) {
//      None
//    } else {
//      val lower = xml \ "lower"
//      val lowerQuantity =
//        if (lower.isEmpty) 0
//        else
//          intOrError(
//            lower,
//            s"Expected a single integer for <lower>; found: '${lower.text}'")
//
//      val upper = xml \ "upper"
//      val upperQuantity = intOrError(
//        upper,
//        s"Expected a single integer for <upper>; found: '${upper.text}'")
//      val step = xml \ "step"
//      val stepQuantity =
//        intOrError(
//          step,
//          s"Expected a single integer for <step>; found: '${step.text}'")
//
//      Some(StressBounded(lowerQuantity, upperQuantity, stepQuantity))
//    }
//  }
//
//  private def parseStressSingular(xml: NodeSeq): Option[StressConfiguration] = {
//    if (xml.isEmpty) {
//      None
//    } else {
//      val singular = intOrError(
//        xml,
//        s"Expected a single integer for <singular>; found: '${xml.text}'")
//      Some(StressSingular(singular))
//    }
//  }
//
//  private def parseStressListed(xml: NodeSeq): Option[StressConfiguration] = {
//    if (xml.isEmpty) {
//      None
//    } else {
//      if (xml.text.matches("[0-9]+(,[0-9]+)+")) {
//        Some(StressList(xml.text.split(',').map(s => s.trim.toInt).toList))
//      } else {
//        error(
//          "Invalid input for <list>; expected a comma-separated list of integers"
//        )
//      }
//    }
//  }
}
