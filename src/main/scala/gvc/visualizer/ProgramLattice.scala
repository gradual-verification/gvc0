package gvc.visualizer
import gvc.ExecutionMetrics
import scala.collection.mutable

object ProgramLattice {

  def executeProgramLattice(
      permList: List[List[PermutedProgram]]
  ): List[List[ExecutionMetrics]] = ???

  def generateProgramLattice(
      permList: List[PermutedProgram]
  ): List[List[PermutedProgram]] = {
    def getLevel(perm: PermutedProgram): Int =
      perm.nCLausesLoopInvariants + perm.nClausesPreconditions + perm.nClausesPostconditions + perm.nClausesAssertions
    def getListLevel(lst: mutable.ListBuffer[PermutedProgram]): Int = {
      if (lst.nonEmpty) {
        getLevel(lst.head)
      } else {
        0
      }
    }
    object LevelOrdering extends Ordering[mutable.ListBuffer[PermutedProgram]] {
      override def compare(
          x: mutable.ListBuffer[PermutedProgram],
          y: mutable.ListBuffer[PermutedProgram]
      ): Int = {
        getListLevel(x) compare getListLevel(y)
      }
    }
    val lattice =
      mutable.TreeSet[mutable.ListBuffer[PermutedProgram]]()(LevelOrdering)
    permList.foreach(elem => {
      val levelExists =
        lattice.find(buffer => getListLevel(buffer) == getLevel(elem))
      if (levelExists.isDefined) {
        levelExists.get += elem
      } else {
        lattice += mutable.ListBuffer(elem)
      }
    })

    lattice.map(lst => lst.toList).toList
  }

  def generateCSV(
      programLattice: List[List[PermutedProgram]],
      performanceLattice: List[List[ExecutionMetrics]],
      filePath: String
  ) = ???

  def generateTikZ(
      programLattice: List[List[PermutedProgram]],
      performanceLattice: List[List[ExecutionMetrics]],
      filePath: String
  ) = ???
}
