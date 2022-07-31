package gvc.benchmarking

import gvc.Config
import gvc.Config.error
import gvc.transformer.IR

object BenchmarkRecreator {

  def recreate(config: RecreatorConfig,
               baseConfig: Config,
               libraries: List[String]): IR.Program = {
    val conn = DAO.connect(config.db, config)
    val syncedPrograms =
      BenchmarkPopulator.sync(config.sources, libraries, conn)
    val permutation = DAO.resolvePermutation(config.permToRecreate, conn)

    permutation match {
      case Some(perm) =>
        if (syncedPrograms.contains(perm.programID)) {
          val correspondingProgramLabels =
            syncedPrograms(perm.programID).labels

          val asLabelSet =
            LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                                  perm.permutationHash)
          new SelectVisitor(syncedPrograms(perm.programID).ir).visit(asLabelSet)

        } else {
          error(
            s"The program that this permutation was derived from was not found.")
        }
      case None =>
        error(
          s"A permutation with ID=${baseConfig.recreatePerm.get} does not exist in the database.")
    }

  }
}
