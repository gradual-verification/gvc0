package gvc.weaver
import gvc.transformer.IR
import gvc.transformer.SilverProgram

class WeaverException(message: String) extends Exception(message)

object Weaver {
  def weave(ir: IR.Program, silver: SilverProgram): Unit = {
    Checker.insert(Collector.collect(ir, silver))
  }
}
