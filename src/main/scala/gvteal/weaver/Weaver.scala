package gvteal.weaver
import gvteal.transformer.IR
import gvteal.transformer.SilverProgram

class WeaverException(message: String) extends Exception(message)

object Weaver {
  def weave(ir: IR.Program, silver: SilverProgram): Unit = {
    Checker.insert(Collector.collect(ir, silver))
  }
}
