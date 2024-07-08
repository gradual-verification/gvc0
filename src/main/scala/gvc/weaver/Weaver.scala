package gvc.weaver
import gvc.transformer.IR
import viper.silver.{ast => vpr}

class WeaverException(message: String) extends Exception(message)

object Weaver {
  def weave(ir: IR.Program, silver: vpr.Program): Unit = {
    val collected = Collector.collect(ir, silver)
    /*
      // Dump collected checks (uncomment for debugging)
      for ((k, v) <- collected.methods) {
        System.out.println(k + "\n--------------------\n")
        RuntimeCheck.dump(v.checks)
        System.out.print("\n\n")
      }
    */
    val scoped = CheckScope.scope(collected)
    val deps = Dependencies.calculate(scoped)
    Checker.insert(deps)
  }
}
