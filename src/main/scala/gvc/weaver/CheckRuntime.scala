package gvc.weaver

import scala.io.Source
import fastparse.Parsed.{Failure, Success}
import gvc.parser.Parser
import gvc.analyzer.{ErrorSink, ResolvedProgram, Resolver}
import gvc.transformer.{DependencyTransformer, IR}
object CheckRuntime {
  val name = "runtime"
  private lazy val header: ResolvedProgram = {
    val runtimeSource = Source.fromResource(name + ".h0").mkString
    val parsed = Parser.parseProgram(runtimeSource) match {
      case _: Failure =>
        throw new WeaverException("Cannot parse runtime header")
      case Success(value, _) => value
    }

    val errors = new ErrorSink()
    val resolved = Resolver.resolveProgram(parsed, List(), errors)
    if (errors.errors.nonEmpty)
      throw new WeaverException("Cannot resolve runtime header")

    resolved
  }

  def addToIR(program: IR.Program): CheckRuntime = {
    val dependency = program.addDependency(name, isLibrary = true)
    DependencyTransformer.transform(program, dependency, header)
    new CheckRuntime(program)
  }

  object Names {
    val ownedFieldsStruct = "OwnedFields"
    val fieldArray = "FieldArray"
    val primaryOwnedFields = "_ownedFields"
    val temporaryOwnedFields = "_tempFields"
    val contextOwnedFields = "_contextFields"
    val initOwnedFields = "runtime_init"
    val addStruct = "runtime_addAll"
    val remove = "runtime_remove"
    val join = "runtime_join"
    val assert = "runtime_assert"
    val add = "runtime_add"
    val instanceCounter = "_instanceCounter"
    val id = "_id"
  }
}

class CheckRuntime private (program: IR.Program) {
  import CheckRuntime.Names
  val ownedFields: IR.StructDefinition =
    program.struct(Names.ownedFieldsStruct)
  val ownedFieldsRef = new IR.ReferenceType(ownedFields)
  val init: IR.MethodDefinition =
    program.method(Names.initOwnedFields)
  val addStruct: IR.MethodDefinition =
    program.method(Names.addStruct)
  val add: IR.MethodDefinition =
    program.method(Names.add)
  val remove: IR.MethodDefinition = program.method(Names.remove)
  val join: IR.MethodDefinition = program.method(Names.join)
  val assert: IR.MethodDefinition = program.method(Names.assert)
}
