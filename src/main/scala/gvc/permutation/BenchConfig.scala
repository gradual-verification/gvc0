package gvc.permutation

import gvc.{Config, Main}
import gvc.permutation.Bench.{BenchmarkException, Names}
import gvc.permutation.Extensions.{c0, csv}
import gvc.transformer.IRGraph

import java.math.BigInteger
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable

object BenchConfig {

  case class BenchmarkConfig(
      files: BenchmarkOutputFiles,
      prior: BenchmarkPrior,
      workload: BenchmarkWorkload,
      ir: IRGraph.Program,
      labels: List[ASTLabel],
      rootConfig: Config
  )

  case class BenchmarkWorkload(
      iterations: Int,
      wUpper: Int,
      wStep: Int,
      wList: List[Int],
      nPaths: Int
  )

  case class BenchmarkPrior(
      visitedPaths: Set[BigInteger],
      visitedPermutations: Set[BigInteger]
  )

  case class BenchmarkOutputFiles(
      root: Path,
      perms: Path,
      verifiedPerms: Path,
      pathDescriptions: Path,
      baselinePerms: Option[Path],
      logs: Path,
      verifyLogs: Path,
      baselineCompilationLogs: Path,
      execLogs: Path,
      baselineExecLogs: Path,
      compilationLogs: Path,
      performance: Path,
      baselinePerformance: Path,
      levels: Path,
      metadata: Path,
      source: Path,
      permMap: Path
  )

  case class TaggedPath(hash: BigInteger, source: Path)

  private def resolveCompletedPermutations(
      files: BenchmarkOutputFiles,
      template: List[ASTLabel]
  ): Set[TaggedPath] = {
    val permSet = mutable.Set[String]()
    Files
      .list(files.perms)
      .filter(!Files.isDirectory(_))
      .forEach(path =>
        permSet.add(Extensions.remove(path.getFileName.toString))
      )
    val verifiedPermSet = mutable.Set[String]()
    Files
      .list(files.verifiedPerms)
      .filter(path => !Files.isDirectory(path))
      .forEach(path =>
        verifiedPermSet.add(Extensions.remove(path.getFileName.toString))
      )
    files.baselinePerms match {
      case Some(value) =>
        Files
          .list(value)
          .filter(path => !Files.isDirectory(path))
          .forEach(path =>
            verifiedPermSet.add(Extensions.remove(path.getFileName.toString))
          )
      case None =>
    }
    val incomplete = permSet.diff(verifiedPermSet)
    incomplete.foreach(name => {
      Files.deleteIfExists(files.perms.resolve(c0(name)))
      Files.deleteIfExists(files.verifiedPerms.resolve(c0(name)))
      files.baselinePerms match {
        case Some(value) => Files.deleteIfExists(value.resolve(c0(name)))
        case None        =>
      }
    })
    permSet += LabelTools
      .createID(template, template.toSet)
      .toString(16)
    permSet += LabelTools.createID(template, Set.empty).toString(16)
    verifiedPermSet
      .intersect(permSet)
      .map(LabelTools.parseID)
      .filter(_.isDefined)
      .map(id => TaggedPath(id.get, files.perms.resolve(c0(id.get))))
      .toSet
  }

  private def resolveCompletedPathsDescriptions(
      pathDir: Path,
      template: List[ASTLabel],
      completedHashes: Set[BigInteger]
  ): mutable.Map[Int, TaggedPath] = {
    val mapping = mutable.Map[Int, TaggedPath]()
    if (Files.exists(pathDir)) {
      val contents = pathDir.toFile
        .listFiles()
        .filter(_.isFile)
        .toList
      contents.foreach(file => {
        val pathID = Extensions.remove(file.getName)
        if (pathID.matches("[0-9]+")) {
          val pathContents = Files.readString(file.toPath).trim
          if (pathContents.matches("/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/")) {
            val contentsFiltered = pathContents
              .substring(
                pathContents.indexOf("/*") + 2,
                pathContents.lastIndexOf("*/")
              )
              .trim
              .split("\n")
              .map(_.trim)
            val contentsMatched = contentsFiltered
              .map(hash => template.find(label => label.hash.equals(hash)))
              .filter(_.isDefined)
            val pathHash = LabelTools
              .hashPath(template, contentsMatched.map(_.get).toList)
            if (
              contentsFiltered.length == contentsMatched.length && completedHashes
                .contains(pathHash)
            ) {
              mapping += (pathID.toInt -> TaggedPath(
                pathHash,
                file.toPath
              ))
            } else if (contentsFiltered.length != contentsMatched.length) {
              throw new BenchmarkException(
                s"The path description ${file.toPath.toString} doesn't match the source provided."
              )
            }
          } else {
            throw new BenchmarkException(
              s"The path description ${file.toPath.toString} is incorrectly formatted."
            )
          }
        }
      })
    }
    mapping
  }

  private def reconstructMetadataEntries(
      template: List[ASTLabel],
      tags: Set[TaggedPath],
      libraryPaths: List[String]
  ): List[List[String]] = {
    val visitor = new LabelVisitor()
    tags
      .map(tag => {
        val src = Files.readString(tag.source)
        val ir = Main.generateIR(src, libraryPaths)
        val labels = visitor.visit(ir)
        CSVIO
          .generateMetadataColumnEntry(
            tag.hash.toString(16),
            template.toSet,
            labels.toSet
          )
      })
      .toList
  }

  private def resolvePriorBenchmark(
      labels: List[ASTLabel],
      files: BenchmarkOutputFiles,
      libraryDirs: List[String]
  ): BenchmarkPrior = {

    val hashEntries =
      CSVIO.readEntries(files.permMap, Columns.pathColumnNames)

    val validHashEntryPairs = hashEntries
      .map(entry => (LabelTools.parseID(entry(1)), entry))
      .filter(_._1.isDefined)

    val completedHashes = validHashEntryPairs.map(_._1.get).toSet
    val completedEntries = validHashEntryPairs.map(_._2)

    CSVIO.writeEntries(
      files.permMap,
      completedEntries,
      Columns.pathColumnNames
    )

    val potentiallyCompletedPaths = resolveCompletedPathsDescriptions(
      files.pathDescriptions,
      labels,
      completedHashes
    )

    val completedPermutations = resolveCompletedPermutations(files, labels)

    val pathIndex = Columns.mappingColumnNames.indexOf("path_id")
    val stepIndex = Columns.mappingColumnNames.indexOf("level_id")
    val integerRegex = "[0-9]+"

    val entries = CSVIO.readEntries(files.levels, Columns.mappingColumnNames)

    //group by path_id
    val groups =
      entries
        .filter(entry =>
          entry.head.matches(LabelTools.hexRegex) && entry(pathIndex)
            .matches(integerRegex) && completedPermutations
            .map(_.hash)
            .contains(new BigInteger(entry.head, 16))
        )
        .groupBy(_(pathIndex))

    //find the number of steps per path, filtering out paths with corrupted step indices
    val max =
      if (entries.nonEmpty)
        entries
          .filter(_(stepIndex).matches("[0-9]+"))
          .map(_(stepIndex).toInt)
          .max + 1
      else 0

    //select only completed paths
    val validPathGroups = groups.filter(_._2.length == max)

    val validEntries =
      validPathGroups.values
        .flatten(entryCollection => {
          entryCollection
        })
        .toList

    CSVIO.writeEntries(files.levels, validEntries, Columns.mappingColumnNames)
    val validPerms =
      validPathGroups.values.flatten.toList
        .map(lst => LabelTools.parseID(lst.head))
        .filter(_.isDefined)
        .map(_.get)
        .toSet

    val metadataColumns = Columns.metadataColumnNames(labels)
    val metadataEntries =
      CSVIO.readEntries(files.metadata, Columns.metadataColumnNames(labels))

    val validMetadataPairs: List[(BigInteger, List[String])] = metadataEntries
      .map(entry => {
        LabelTools.parseID(entry.head) match {
          case Some(value) if validPerms.contains(value) =>
            Some(value, entry)
          case _ => None
        }
      })
      .filter(_.isDefined)
      .map(_.get)
    val validMetadataPermIDs = validMetadataPairs.map(_._1).toSet
    val validMetadataEntries = validMetadataPairs.map(_._2)

    val missingMetadataIDs = validPerms.diff(validMetadataPermIDs)
    val recreationPaths =
      completedPermutations.filter(tag => missingMetadataIDs.contains(tag.hash))
    val reconstructedMetadataEntries =
      reconstructMetadataEntries(labels, recreationPaths, libraryDirs)

    CSVIO.writeEntries(
      files.metadata,
      validMetadataEntries ++ reconstructedMetadataEntries,
      metadataColumns
    )

    val validPathIndices = validPathGroups.keySet.map(_.toInt)
    val pathHashes = mutable.Set[BigInteger]()

    potentiallyCompletedPaths.keys.foreach(key => {
      if (validPathIndices.contains(key)) {
        pathHashes += potentiallyCompletedPaths(key).hash
      } else {
        Files.delete(potentiallyCompletedPaths(key).source)
      }
    })
    BenchmarkPrior(
      pathHashes.toSet,
      validPerms
    )
  }

  private def resolveOutputFiles(
      inputSource: String,
      config: Config
  ): BenchmarkOutputFiles = {
    val dir = config.compileBenchmark.get
    val disableBaseline = config.disableBaseline

    val root = Paths.get(dir)
    Files.createDirectories(root)

    val existingSource = root.resolve(Names.source)

    if (Files.exists(existingSource)) {
      if (!Files.readString(existingSource).equals(inputSource))
        Config.error(
          s"The existing permutation directory ${existingSource.getParent.toAbsolutePath} was created for a different source file than the one provided"
        )
    } else {
      Main.writeFile(existingSource.toString, inputSource)
    }

    val perms = root.resolve(Names.perms)
    Files.createDirectories(perms)

    val pathDescriptions = root.resolve(Names.pathDesc)
    Files.createDirectories(pathDescriptions)

    val verifiedPerms = root.resolve(Names.verified_perms)
    Files.createDirectories(verifiedPerms)

    val baselinePerms: Option[Path] = if (!disableBaseline) {
      val dir = root.resolve(Names.baselinePerms)
      Files.createDirectories(dir)
      Some(dir)
    } else {
      None
    }

    val performance = root.resolve(Names.performance)
    val baselinePerformance = root.resolve(Names.baselinePerformance)
    val levels = root.resolve(Names.levels)
    val metadata = root.resolve(Names.metadata)
    val permMap = root.resolve(csv(Names.perms))
    val logs = root.resolve(Names.logs)
    Files.createDirectories(logs)

    val verifyLog = logs.resolve(Names.verifyLogs)
    val compileLog = logs.resolve(Names.compilationLogs)
    val baselineCompileLog = logs.resolve(Names.baselineCompilationLogs)

    val exec = logs.resolve(Names.execLogs)
    val baselineExec = logs.resolve(Names.baselineExecLogs)

    BenchmarkOutputFiles(
      root = root,
      perms = perms,
      verifiedPerms = verifiedPerms,
      baselinePerms = baselinePerms,
      logs = logs,
      verifyLogs = verifyLog,
      compilationLogs = compileLog,
      baselineCompilationLogs = baselineCompileLog,
      execLogs = exec,
      baselineExecLogs = baselineExec,
      performance = performance,
      baselinePerformance = baselinePerformance,
      levels = levels,
      metadata = metadata,
      pathDescriptions = pathDescriptions,
      source = existingSource,
      permMap = permMap
    )
  }

  def resolveWorkload(config: Config): BenchmarkWorkload =
    BenchmarkWorkload(
      config.benchmarkIterations.getOrElse(1),
      config.benchmarkWUpper.getOrElse(32),
      config.benchmarkWStep.getOrElse(8),
      config.benchmarkWList.getOrElse(List()),
      config.benchmarkPaths.getOrElse(1)
    )

  def resolveBenchmarkConfig(
      source: String,
      librarySearchPaths: List[String],
      config: Config
  ): BenchmarkConfig = {
    val ir = Main.generateIR(source, librarySearchPaths)
    val labeller = new LabelVisitor()
    val labels = labeller.visit(ir)
    val files = resolveOutputFiles(source, config)
    val prior = resolvePriorBenchmark(labels, files, librarySearchPaths)
    val work = resolveWorkload(config)
    BenchmarkConfig(
      files = files,
      prior = prior,
      ir = ir,
      labels = labels,
      workload = work,
      rootConfig = config
    )
  }
}
