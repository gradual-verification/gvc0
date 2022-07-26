package gvc.benchmarking
import gvc.benchmarking.Extensions.{c0, csv, log, out}

import scala.util.matching.Regex

object Benchmark {
  val arbitraryStressDeclaration: Regex = "(int )?(stress = [0-9]+;)".r
  val correctStressDeclaration: Regex =
    "(int[ ]+main\\(\\s*\\)\\s\\{[\\s\\S]*\n\\s*int stress = [0-9]+;)".r
  class BenchmarkException(message: String) extends Exception(message)
  val readStress =
    "int readStress() {int* value = alloc(int); args_int(\"--stress\", value); args_t input = args_parse(); printint(*value); return *value;}\n"
  object Names {
    val conjuncts: String = csv("conjuncts")
    //
    val perms = "perms"
    val verifiedPerms = "perms_verified"
    val dynamicPerms = "perms_full_dynamic"
    val framingPerms = "perms_only_framing"
    //
    val pathDesc = "path_desc"

    val executionPerformanceGradual: String = csv("dyn_perf_gradual")
    val executionPerformanceDynamic: String = csv("dyn_perf_full_dynamic")
    val executionPerformanceFraming: String = csv("dyn_perf_only_framing")

    val verificationPerformance: String = csv("verification_perf")
    val instrumentationPerformance: String = csv("instrumentation_perf")

    val compilationPerformanceGradual: String = csv("compilation_perf_gradual")
    val compilationPerformanceDynamic: String = csv(
      "compilation_perf_full_dynamic"
    )
    val compilationPerformanceFraming: String = csv(
      "compilation_perf_only_framing"
    )
    val translationPerformance: String = csv("translation_perf")

    val levels: String = csv("levels")
    val metadata: String = csv("metadata")
    //
    val verifyLogs: String = log("verify")
    val compilationLogs: String = log("cc0")
    val dynamicCompilationLogs: String = log("cc0_full_dynamic")
    val framingCompilationLogs: String = log("cc0_only_framing")
    //
    val execLogs: String = log("exec")
    val dynamicExecLogs: String = log("exec_full_dynamic")
    val framingExecLogs: String = log("exec_only_framing")
    //
    val source: String = c0("source")
    val logs = "logs"
    val stressDeclaration = "stress"
    val entry = "main"
    val tempC0File: String = c0("temp")
    val tempBinaryFile: String = out("temp")
  }
  def injectStress(source: String): String = {
    val withStressDeclaration = correctStressDeclaration.replaceFirstIn(
      source,
      readStress + "int main()\n{\nint stress = readStress();\n"
    )
    val removedAdditionalAssignments =
      arbitraryStressDeclaration.replaceAllIn(withStressDeclaration, "")
    "#use <conio>\n#use <args>\n" + removedAdditionalAssignments
  }
  def isInjectable(source: String): Boolean = {
    correctStressDeclaration
      .findAllMatchIn(source)
      .nonEmpty
  }
}
