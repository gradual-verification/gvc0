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
    val initOwnedFields = "initOwnedFields"
    val addStructAcc = "addStructAcc"
    val addAcc = "addAcc"
    val loseAcc = "loseAcc"
    val join = "join"
    val assertAcc = "assertAcc"
    val addAccEnsureSeparate = "addAccEnsureSeparate"
    val find = "find"
    val instanceCounter = "_instanceCounter"
    val id = "_id"
    val removePrefix = "remove_"
    val addPrefix = "add_"
    val checkPrefix = "check_"
  }
}

class CheckRuntime private (program: IR.Program) {
  import CheckRuntime.Names
  val ownedFields: IR.StructDefinition =
    program.struct(Names.ownedFieldsStruct)
  val ownedFieldsRef = new IR.ReferenceType(ownedFields)
  val initOwnedFields: IR.MethodDefinition =
    program.method(Names.initOwnedFields)
  val addStructAcc: IR.MethodDefinition =
    program.method(Names.addStructAcc)
  val addAcc: IR.MethodDefinition = program.method(Names.addAcc)
  val addAccEnsureSeparate: IR.MethodDefinition =
    program.method(Names.addAccEnsureSeparate)
  val loseAcc: IR.MethodDefinition = program.method(Names.loseAcc)
  val join: IR.MethodDefinition = program.method(Names.join)
  val assertAcc: IR.MethodDefinition = program.method(Names.assertAcc)
  val find: IR.MethodDefinition = program.method(Names.find)
}
