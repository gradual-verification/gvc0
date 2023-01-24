package gvc.benchmarking

import gvc.Config
import gvc.Config.error

import java.nio.file.{Files, Path, Paths, StandardCopyOption}
import scala.sys.process.Process

class GProf(binary: Path, destination: Path) {
  private val gprof_exe = Config.resolveToolPath("gprof", "GPROF_EXE")
  private val profilingOutput = Paths.get("./gmon.out")
  private val profilingSum = Paths.get("./gmon.sum")

  def merge: Unit = {
    if (Files.exists(destination)) {
      val command =
        s"${gprof_exe} -s ${binary.toAbsolutePath}  ${profilingOutput.toAbsolutePath} ${destination.toAbsolutePath}"
      val commandAsProcess = Process(command)
      val exit = commandAsProcess.run().exitValue()
      if (exit != 0) {
        error(s"Failed to merge gprof output to ${destination.toString}")
      } else {
        Files.copy(profilingSum,
                   destination,
                   StandardCopyOption.REPLACE_EXISTING)
      }
    } else {
      Files.copy(profilingOutput, destination)
    }
  }
}
