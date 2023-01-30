package gvc.benchmarking

import gvc.benchmarking.Benchmark.Extensions.{c0, csv}

import scala.util.matching.Regex

object Benchmark {
  object Extensions {
    def c0(basename: Object): String = basename.toString + ".c0"
    def txt(basename: String): String = basename + ".txt"
    def out(basename: String): String = basename + ".out"

    def csv(basename: String): String = basename + ".csv"

    def log(basename: String): String = basename + ".log"
    def sum(basename: String): String = basename + ".sum"
    def remove(fullname: String): String =
      fullname.replaceFirst("[.][^.]+$", "")
  }
  val arbitraryStressDeclaration: Regex = {
    "(int )?(stress = [0-9]+;)".r
  }
  val correctStressDeclaration: Regex = {
    "(int +main\\(\\s*\\)\\s\\{[\\s\\S]*\n\\s*int stress = [0-9]+;)".r
  }
  class BenchmarkException(message: String) extends Exception(message)
  val readStress =
    "int readStress() {int* value = alloc(int); args_int(\"--stress\", value); args_t input = args_parse(); printint(*value); return *value;}\n"
  object Names {
    val conjuncts: String = csv("conjuncts")
    val perms = "perms"
    val metadata: String = csv("metadata")
    val source: String = c0("source")
    val entry = "main"
  }
  def injectStress(source: String): String = {
    val withStressDeclaration = correctStressDeclaration.replaceFirstIn(
      source,
      readStress + "int main()\n{\nint stress = readStress();\nprintint(stress);\n"
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
