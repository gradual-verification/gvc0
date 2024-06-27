package gvc.weaver
import gvc.transformer.IR
import viper.silver.{ast => vpr}

class WeaverException(message: String) extends Exception(message)

object Weaver {
  def weave(ir: IR.Program, silver: vpr.Program): Unit = {
    val collected = Collector.collect(ir, silver)
    val scoped = CheckScope.scope(collected)
    val deps = Dependencies.calculate(scoped)
    Checker.insert(deps)
  }
}
