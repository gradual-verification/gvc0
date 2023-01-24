package gvc.benchmarking

import gvc.Config
import gvc.Config.error

import java.nio.file.{Files, Path}
import scala.sys.process.Process

class GProf(binary: Path, destination: Path) {
  private val gprof_exe = Config.resolveToolPath("gprof", "GPROF_EXE")
  private val profilingName = "gmon.out"
  private def resolveProfilingOutput(exe: Path): Path = {
    exe.getParent.toAbsolutePath.resolve(profilingName)
  }
  def merge: Unit = {
    val profilingOutput = resolveProfilingOutput(binary)
    if (Files.exists(destination)) {
      val command =
        s"${gprof_exe} -s ${gprof_exe}  ${profilingOutput.toAbsolutePath} ${destination.toAbsolutePath}"
      val commandAsProcess = Process(command)
      val exit = commandAsProcess.run().exitValue()
      if (exit != 0) {
        error(s"Failed to merge gprof output to ${destination.toString}")
      }
    } else {
      Files.copy(profilingOutput, destination)
    }
  }
}
