package gvc.benchmarking

import gvc.Config
import gvc.Config.error
import gvc.transformer.IR

object BenchmarkRecreator {
  def recreate(config: RecreatorConfig,
               baseConfig: Config,
               libraries: List[String]): IR.Program = {
    val conn = DAO.connect(config.db)
    val permutation = DAO.resolvePermutation(config.permToRecreate, conn)
    permutation match {
      case Some(perm) =>
        Output.success(s"Located permutation #${config.permToRecreate}")
        val pInfo = BenchmarkPopulator
          .syncIndividual(config.sources, libraries, conn, perm.programID)
        val correspondingProgramLabels = pInfo.labels
        val asLabelSet =
          LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                                perm.permutationContents)
        new SelectVisitor(pInfo.ir)
          .visit(asLabelSet)
      case None =>
        error(
          s"A permutation with ID=${baseConfig.recreatePerm.get} does not exist in the database.")
    }
  }
}
