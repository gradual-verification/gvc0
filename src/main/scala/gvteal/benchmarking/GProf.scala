package gvteal.benchmarking

import gvteal.Config
import gvteal.Config.error

import java.nio.file.{Files, Path, Paths}
import scala.sys.process.{Process, ProcessLogger}

class GProf(binary: Path, destination: Path) {
  private val gprof_exe = Config.resolveToolPath("gprof", "GPROF_EXE")
  private val profilingOutput = Paths.get("./gmon.out")
  Files.deleteIfExists(profilingOutput)
  private val profilingSum = Paths.get("./gmon.sum")
  Files.deleteIfExists(profilingSum)
 
  def merge(): Unit = {
    if (Files.exists(profilingSum)) {
      val command =
        s"${gprof_exe} -s ${binary.toAbsolutePath}  ${profilingOutput.toAbsolutePath} ${profilingSum.toAbsolutePath}"
      val commandAsProcess = Process(command)
      val exit = commandAsProcess.run().exitValue()
      if (exit != 0) {
        error(s"Failed to merge gprof output into ${profilingSum.toString}")
      } else {
        Files.deleteIfExists(profilingOutput)
      }
    } else {
      Files.copy(profilingOutput, profilingSum)
    }
  }

  def complete(): Unit = {
    val output = if (Files.exists(profilingSum)) {
      profilingSum
    } else if (Files.exists(profilingOutput)) {
      profilingOutput
    } else {
      error(
        s"Unable to save gprof results; profiling output file does not exist.")
    }
    var capture = ""
    val logger = ProcessLogger(
      (o: String) => capture += o,
      (e: String) => capture += e
    )
    val command =
      s"${gprof_exe} --brief ${binary.toAbsolutePath} ${output.toAbsolutePath}"
    val commandAsProcess = Process(command)
    val exit = commandAsProcess.run(logger).exitValue()
    if (exit != 0) {
      error(s"Failed to save gprof results into ${destination.toString}")
    } else {
      Files.deleteIfExists(output)
      Files.writeString(destination, capture)
    }
  }
}
