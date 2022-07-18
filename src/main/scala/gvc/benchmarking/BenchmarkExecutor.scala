package gvc.benchmarking

import gvc.benchmarking.DAO.Permutation
import gvc.transformer.IRPrinter
import gvc.{Config, Main}

import java.nio.file.{Files, Paths}

object BenchmarkExecutor {

  case class ReservedProgram(perm: Permutation, stress: Int, perfID: Long)

  def execute(config: ExecutorConfig, baseConfig: Config): Unit = {
    val conn = DAO.connect(config.db)
    val storedVersion = DAO.addOrResolveVersion(config.version, conn)
    val storedHardware = DAO.addOrResolveHardware(config.hardware, conn)
    val libraries = Main.Defaults.includeDirectories

    val syncedPrograms =
      BenchmarkPopulator.syncPrograms(config.sources, libraries, conn)

    val workload = config.workload
    val tempBinary = Paths.get(Main.Defaults.outputFileCollection.binaryName)
    val tempSource = Paths.get(Main.Defaults.outputFileCollection.c0FileName)
    val worklist =
      BenchmarkExternalConfig.generateStressList(config.workload.stress)
    var reservedProgram =
      DAO.reserveProgram(storedVersion, storedHardware, worklist, conn)

    while (reservedProgram.nonEmpty) {
      val reserved = reservedProgram.get
      val correspondingProgramLabels = syncedPrograms(reserved.perm.programID).info.labels

      val asLabelSet = LabelTools.permutationIDToPermutation(
        correspondingProgramLabels,
        reserved.perm.permutationHash)

      val convertedToIR = new SelectVisitor(
        syncedPrograms(reserved.perm.programID).info.ir).visit(asLabelSet)
      val reconstructedSourceText =
        IRPrinter.print(convertedToIR, includeSpecs = false)

      Files.writeString(tempSource, reconstructedSourceText)

      Timing.verifyTimed(reconstructedSourceText,
                         Main.Defaults.outputFileCollection,
                         baseConfig)

      Timing.compileTimed(tempSource,
                          tempBinary,
                          baseConfig,
                          workload.iterations)

      val executionOutput =
        Timing.execTimed(tempBinary,
                         workload.iterations,
                         List(s"--stress=${reserved.stress}"))

      DAO.updatePerformance(reserved.perfID, executionOutput, conn)

      reservedProgram =
        DAO.reserveProgram(storedVersion, storedHardware, worklist, conn)
    }
  }
}
