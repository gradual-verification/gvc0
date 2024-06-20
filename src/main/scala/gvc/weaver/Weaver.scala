package gvc.weaver
import gvc.transformer.IR
import viper.silver.{ast => vpr}

class WeaverException(message: String) extends Exception(message)

object Weaver {
  def weave(ir: IR.Program, silver: vpr.Program): Unit = {
    Checker.insert(Collector.collect(ir, silver))
  }
}
