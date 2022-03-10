package gvc.permutation

import gvc.{Config, Main}
import gvc.transformer.GraphPrinter
import gvc.permutation.SamplingHeuristic.SamplingHeuristic

import java.io.FileWriter
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.reflect.io.Directory
import java.math.BigInteger

object Permute {
  private object Names {
    val _baseline = "baseline.c0"
    val _top = "top.c0"
    val _imprecise_bottom = "bot_imp.c0"
    val _precise_bottom = "bot.c0"
    val _defaultPermuteDumpDir = "./perms"
    val _defaultMetadataFilename = "./perms.csv"
    val _defaultMappingFilename = "./levels.csv"
  }

  case class PermuteOutputFiles(
      permDumpDir: Path,
      metadata: Path,
      mapping: Path
  )

  private def resolveOutputFiles(config: Config): PermuteOutputFiles = {
    val dumpDir =
      Paths.get(config.permuteDumpDir.getOrElse(Names._defaultPermuteDumpDir))
    new Directory(dumpDir.toFile).deleteRecursively()
    Files.createDirectories(dumpDir)

    val metadata = dumpDir.resolve(Names._defaultMetadataFilename)
    val mapping = dumpDir.resolve(Names._defaultMappingFilename)
    PermuteOutputFiles(dumpDir, metadata, mapping)
  }

  def exec(
      source: String,
      config: Config,
      heuristic: SamplingHeuristic
  ): Unit = {
    val ir = Main.generateIR(source)
    val files = resolveOutputFiles(config)
    val selector = new SelectVisitor(ir)

    val outputBottomPrecise =
      files.permDumpDir.resolve(Names._precise_bottom)
    Main.writeFile(
      outputBottomPrecise.toString,
      GraphPrinter.print(ir, includeSpecs = false)
    )

    val outputBottomImprecise =
      files.permDumpDir.resolve(Names._imprecise_bottom)
    Main.writeFile(
      outputBottomImprecise.toString,
      GraphPrinter.print(
        selector.visit(mutable.TreeSet.empty[Int]),
        includeSpecs = true
      )
    )

    val outputTop = files.permDumpDir.resolve(Names._top)
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(ir, includeSpecs = true)
    )
    val labeller = new LabelVisitor()
    val labels = labeller.visit(ir)

    val alreadySampled = mutable.Set[String]()
    val csv = new CSVPrinter(files, labels)
    var previousID: Option[String] = None

    for (sampleIndex <- 0 until config.permute.get) {

      val sampleToPermute = LabelTools.sample(labels, heuristic)
      val currentPermutation = mutable.TreeSet()(LabelOrdering)
      val permutationIndices = mutable.TreeSet[Int]()
      for (labelIndex <- 0 to sampleToPermute.length - 2) {
        currentPermutation += sampleToPermute(labelIndex)
        permutationIndices += sampleToPermute(labelIndex).exprIndex
        val id = csv.createID(currentPermutation)

        if (previousID.isDefined && previousID.get == id) {
          println(sampleToPermute(labelIndex).hash)
          throw new Exception("invalid step in permutation")
        }

        if (!alreadySampled.contains(id)) {
          val permutationSourceFile =
            files.permDumpDir.resolve(
              id + ".c0"
            )
          val builtPermutation = selector.visit(permutationIndices)
          val permutationSourceText =
            LabelTools.appendPathComment(
              GraphPrinter.print(builtPermutation, includeSpecs = true),
              currentPermutation.toList
            )
          Main.writeFile(
            permutationSourceFile.toString,
            permutationSourceText
          )
          csv.logPermutation(id, currentPermutation)
          alreadySampled += id
        }
        csv.logStep(id, sampleIndex + 1, labelIndex + 1)
        print(
          s"\rGenerated ${alreadySampled.size} unique programs, ${sampleIndex + 1}/${config.permute.get} paths completed..."
        )
        previousID = Some(id)
      }
    }
  }

  class CSVPrinter(files: PermuteOutputFiles, template: List[ASTLabel]) {
    val metaWriter = new FileWriter(files.metadata.toString)
    val mappingWriter = new FileWriter(files.mapping.toString)

    val metadataColumnNames: String =
      (List("id") ++ template.map(_.hash)).foldRight("")(_ + "," + _) + '\n'
    metaWriter.write(metadataColumnNames)

    val mappingColumnNames: String =
      List("id", "path_id", "level_id").foldRight("")(_ + "," + _) + '\n'
    mappingWriter.write(mappingColumnNames)

    def createID(permutation: mutable.TreeSet[ASTLabel]): String = {
      new BigInteger(
        template
          .map(label => {
            (if (permutation.contains(label)) 1 else 0).toString
          })
          .foldRight("")(_ + _),
        2
      ).toString(16)
    }

    def logPermutation(
        id: String,
        permutation: mutable.TreeSet[ASTLabel]
    ): String = {
      val entry = ListBuffer[String](id)
      template.foreach(label => {
        val toAppend = (if (permutation.contains(label)) 1 else 0).toString
        entry += toAppend
      })
      metaWriter.write(entry.foldRight("")(_ + "," + _) + '\n')
      metaWriter.flush()
      id
    }

    def logStep(id: String, pathIndex: Int, levelIndex: Int): Unit = {
      mappingWriter.write(
        List(id, pathIndex, levelIndex).foldRight("")(_ + "," + _) + '\n'
      )
      mappingWriter.flush()
    }
  }
}
