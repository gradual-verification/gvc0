package gvc.benchmarking

import gvc.Config
import gvc.Config.error
import gvc.transformer.IR

object BenchmarkRecreator {

  trait Recreated

  case class RecreatedUnverified(ir: IR.Program) extends Recreated

  case class RecreatedVerified(c0: String) extends Recreated

  def recreate(config: RecreatorConfig,
               baseConfig: Config,
               libraries: List[String],
               conn: DAO.DBConnection,
               permToRecreate: Int): Recreated = {
    val permutation = DAO.resolvePermutation(permToRecreate, conn)

    permutation match {
      case Some(perm) =>
        Output.success(s"Located permutation #${permToRecreate}")

        if (config.modifiers.skipVerification) {
          DAO.resolveVersion(config.version, conn) match {
            case Some(value) =>
              val recreatedSource =
                DAO.resolveVerifiedPermutation(value, perm.id, conn)
              recreatedSource match {
                case Some(value) => RecreatedVerified(value)
                case None =>
                  error(
                    s"This permutation has yet to be statically verified during a benchmarking run.")
              }
            case None => error(s"Unable to resolve version '${config.version}'")
          }

        } else {
          val pInfo = BenchmarkPopulator
            .syncIndividual(config.sources, libraries, conn, perm.programID)
          val correspondingProgramLabels = pInfo.labels
          val asLabelSet =
            LabelTools.permutationIDToPermutation(correspondingProgramLabels,
                                                  perm.permutationContents)
          RecreatedUnverified(
            new SelectVisitor(pInfo.ir)
              .visit(asLabelSet))
        }

      case None =>
        error(
          s"A permutation with ID=${permToRecreate} does not exist in the database.")
    }
  }
}
