package gvc.visualizer
import gvc.Main.{deleteFile, writeFile}
import gvc.{CC0Options, CC0Wrapper, Config, Main, OutputFileCollection}
import java.nio.file.Paths
import scala.collection.mutable

case class Metrics(
    verification: Long,
    execution: Long
)

case class VerifiedProgram(
    verification: Long,
    permutation: ProgramPermutation,
    verifiedSource: String
)

object ProgramLattice {

  private val _columns = List(
    "level",
    "index",
    "n_clauses_preconditions",
    "n_clauses_postconditions",
    "n_clauses_assertions",
    "n_clauses_loop_invariants",
    "verification_time_ns",
    "execution_time_ns"
  ).foldRight("")(_ + "," + _)

  def verifyProgramLattice(
      permList: List[List[ProgramPermutation]],
      fileNames: OutputFileCollection
  ): List[List[VerifiedProgram]] = {
    permList.indices
      .map(i => {
        val level = permList(i)
        level.indices
          .map(j => {
            val permutation = level(j)
            verifyTimed(
              permutation,
              fileNames,
              timedIterations = 10
            )
          })
          .toList
      })
      .toList
  }

  def executeProgramLattice(
      permList: List[List[VerifiedProgram]],
      filename: String,
      config: Config
  ): List[List[Metrics]] = {
    permList.indices
      .map(i => {
        val level = permList(i)
        level.indices
          .map(j => {
            val permutation = level(j)
            val outputExe = config.output.getOrElse("a.out")
            val runtimeInput =
              Paths.get(getClass.getResource("/runtime.c0").getPath)
            val runtimeIncludeDir = runtimeInput.getParent.toAbsolutePath

            val cc0Options = CC0Options(
              compilerPath = Config.resolveToolPath("cc0", "CC0_EXE"),
              saveIntermediateFiles = config.saveFiles,
              output = Some(outputExe),
              includeDirs = List(runtimeIncludeDir.toString + "/")
            )

            val c0FileName = filename + "_" + i + "_" + j
            writeFile(c0FileName, permutation.verifiedSource)
            val executionTime =
              try {
                CC0Wrapper.execTimed(c0FileName, cc0Options, 10)
              } finally {
                if (!config.saveFiles) deleteFile(c0FileName)
              }
            Metrics(permutation.verification, executionTime)
          })
          .toList
      })
      .toList
  }

  def verifyTimed(
      permutation: ProgramPermutation,
      fileNames: OutputFileCollection,
      timedIterations: Int
  ): VerifiedProgram = {
    var duration: Long = 0
    val verifiedIR = Main.verify(permutation.source, fileNames)
    for (_ <- 1 to timedIterations) {
      val start = System.nanoTime()
      Main.verify(permutation.source, fileNames)
      val stop = System.nanoTime()
      duration = (duration + (start - stop)) / 2
    }
    VerifiedProgram(duration, permutation, verifiedIR)
  }
  private def getLevel(perm: ProgramPermutation): Int = {
    perm.nCLausesLoopInvariants + perm.nClausesPreconditions + perm.nClausesPostconditions + perm.nClausesAssertions
  }
  private def getListLevel(lst: mutable.ListBuffer[ProgramPermutation]): Int = {
    if (lst.nonEmpty) {
      getLevel(lst.head)
    } else {
      0
    }
  }

  private object LevelOrdering
      extends Ordering[mutable.ListBuffer[ProgramPermutation]] {
    override def compare(
        x: mutable.ListBuffer[ProgramPermutation],
        y: mutable.ListBuffer[ProgramPermutation]
    ): Int = {
      getListLevel(x) compare getListLevel(y)
    }
  }

  def generateProgramLattice(
      permList: List[ProgramPermutation]
  ): List[List[ProgramPermutation]] = {
    val lattice =
      mutable.TreeSet[mutable.ListBuffer[ProgramPermutation]]()(LevelOrdering)
    for (elem: ProgramPermutation <- permList) {
      val levelExists =
        lattice.find(buffer => getListLevel(buffer) == getLevel(elem))

      levelExists match {
        case Some(level) => level.insert(1, elem)
        case None        => lattice.+=(mutable.ListBuffer(elem))
      }
    }
    lattice.map(lst => lst.toList).toList
  }

  def generateCSV(
      programLattice: List[List[ProgramPermutation]],
      performanceLattice: List[List[Metrics]]
  ): String = {
    List(_columns) + programLattice.indices
      .flatMap(index => {
        programLattice(index).indices.map(levelIndex => {
          val permutation: ProgramPermutation =
            programLattice(index)(levelIndex)
          val metrics: Metrics = performanceLattice(index)(levelIndex)
          List(
            index,
            levelIndex,
            permutation.nClausesPreconditions,
            permutation.nClausesPostconditions,
            permutation.nClausesAssertions,
            permutation.nCLausesLoopInvariants,
            metrics.verification,
            metrics.execution
          ).map(elem => elem.toString).foldRight("")(_ + "," + _)
        })
      })
      .foldRight("")(_ + "\n" + _)
  }
  /*
  def generateTikZ(
      programLattice: List[List[ProgramPermutation]],
      performanceLattice: List[List[Metrics]],
      filePath: String
  ) = ??? */
}
