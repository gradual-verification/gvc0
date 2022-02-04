package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silver.{ast => vpr}

class WeaverException(message: scala.Predef.String) extends Exception(message)

object Weaver {
  def weave(ir: Program, silver: vpr.Program): Unit = {
    Checker.insert(Collector.collect(ir, silver))
  }
}
