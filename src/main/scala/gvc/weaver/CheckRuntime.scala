package gvc.weaver

import scala.io.Source
import fastparse.Parsed.{Failure, Success}
import gvc.parser.Parser
import gvc.analyzer.{ResolvedProgram, ErrorSink, Resolver}
import gvc.transformer.{IRGraph, DependencyTransformer}

object CheckRuntime {
  val name = "runtime"

  private lazy val header: ResolvedProgram = {
    val runtimeSource = Source.fromResource("runtime.h0").mkString
    val parsed = Parser.parseProgram(runtimeSource) match {
      case _: Failure => throw new WeaverException("Cannot parse runtime header")
      case Success(value, _) => value
    }

    val errors = new ErrorSink()
    val resolved = Resolver.resolveProgram(parsed, errors)
    if (errors.errors.nonEmpty)
      throw new WeaverException("Cannot resolve runtime header")
    
    resolved
  }

  def addToIR(program: IRGraph.Program): CheckRuntime = {
    val dependency = program.addDependency(name, isLibrary = true)
    DependencyTransformer.transform(program, dependency, header)
    new CheckRuntime(program)
  }

  object Names {
    val ownedFields = "OwnedFields"
    val fieldArray = "FieldArray"

    val initOwnedFields = "initOwnedFields"
    val addStructAccess = "addStructAccess"
    val addAccess = "addAccess"
    val loseAccess = "loseAccess"
    val join = "join"
    val disjoin = "disjoin"
    val assertAcc = "assertAcc"
    val assertDisjointAcc = "assertDisjointAcc"
    val find = "find"
  }
}

class CheckRuntime private (program: IRGraph.Program) {
  import CheckRuntime.Names

  val ownedFields = program.struct(Names.ownedFields)
  val ownedFieldsRef = new IRGraph.ReferenceType(ownedFields)

  val initOwnedFields = program.method(Names.initOwnedFields)
  val addStructAccess = program.method(Names.addStructAccess)
  val addAccess = program.method(Names.addAccess)
  val loseAccess = program.method(Names.loseAccess)
  val join = program.method(Names.join)
  val disjoin = program.method(Names.disjoin)
  val assertAcc = program.method(Names.assertAcc)
  val assertDisjointAcc = program.method(Names.assertDisjointAcc)
  val find = program.method(Names.find)
}