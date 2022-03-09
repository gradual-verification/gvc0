package gvc.visualizer

import gvc.{Config, Main}
import gvc.transformer.GraphPrinter
import gvc.visualizer.SamplingHeuristic.SamplingHeuristic

import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.reflect.io.Directory


object Permute {
  private object Names {
    val _baseline = "baseline.c0"
    val _top = "top.c0"
    val _imprecise_bottom = "bot_imp.c0"
    val _precise_bottom = "bot.c0"
    val _defaultPermuteDumpDir = "./perms"
    val _defaultMetadataFilename = "./perms.csv"
  }

  case class PermuteOutputFiles(permDumpDir: Path, metadata: Path)

  private def resolveOutputFiles(config: Config):PermuteOutputFiles = {
    val dumpDir = Paths.get(config.permuteDumpDir.getOrElse(Names._defaultPermuteDumpDir))
    new Directory(dumpDir.toFile).deleteRecursively()
    Files.createDirectories(dumpDir)

    val metadata = Paths.get(config.permuteMetadataFile.getOrElse(Names._defaultMetadataFilename))
    PermuteOutputFiles(dumpDir, metadata)
  }

  def exec(source: String, config: Config, heuristic: SamplingHeuristic): Unit = {
    val ir = Main.generateIR(source)
    val files = resolveOutputFiles(config)

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
        PermutationGenerator.generatePermutation(List.empty, ir),
        includeSpecs = true
      )
    )

    val outputTop = files.permDumpDir.resolve(Names._top)
    Main.writeFile(
      outputTop.toString,
      GraphPrinter.print(ir, includeSpecs = true)
    )

    val labels = Labeller.labelAST(ir)
    val alreadySampled = mutable.Set[String]()

    for (sampleIndex <- 0 until config.permute.get) {
      val sampleToPermute = Labeller.sample(labels, heuristic)
      val currentPermutation = mutable.TreeSet()(Labeller.LabelOrdering)
      for (labelIndex <- 0 to sampleToPermute.length - 2) {

        val permutationSourceFile =
         files.permDumpDir.resolve(
            (sampleIndex + 1) + "_" + (labelIndex + 1) + ".c0"
         )
        currentPermutation += sampleToPermute(labelIndex)
        val permutationHash = Labeller.hashPermutation(currentPermutation.toList)
        if(!alreadySampled.contains(permutationHash)){
          val builtPermutation = PermutationGenerator.generatePermutation(
            currentPermutation.toList,
            ir
          )
          val permutationSourceText =
            appendPathComment(
              GraphPrinter.print(builtPermutation, includeSpecs = true),
              currentPermutation.toList
            )
          Main.writeFile(
            permutationSourceFile.toString,
            permutationSourceText
          )
          alreadySampled += permutationHash
          print(s"\rGenerated ${alreadySampled.size} unique programs, ${sampleIndex + 1}/${config.permute.get} paths completed...")

        }
      }
    }
  }
  def appendPathComment(
                         str: String,
                         labels: List[Labeller.ASTLabel]
                       ): String = {
    "/*\n" +
      labels.foldLeft("")(_ + _.hash + '\n') +
      "*/\n" +
      str
  }

}
