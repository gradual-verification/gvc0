package gvc.weaver

import scala.io.Source
import fastparse.Parsed.{Failure, Success}
import gvc.parser.Parser
import gvc.analyzer.{ErrorSink, ResolvedProgram, Resolver}
import gvc.transformer.IRGraph._
import gvc.transformer.{DependencyTransformer, IRGraph}
import scala.collection.mutable
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
    val ownedFieldsStruct = "OwnedFields"
    val fieldArray = "FieldArray"
    val primaryOwnedFields = "_ownedFields"
    val temporaryOwnedFields = "_tempFields"
    val initOwnedFields = "initOwnedFields"
    val addStructAcc = "addStructAcc"
    val addAcc = "addAcc"
    val loseAcc = "loseAcc"
    val addDisjointAcc = "addDisjointAcc"
    val join = "join"
    val disjoin = "disjoin"
    val assertAcc = "assertAcc"
    val assertDisjointAcc = "assertDisjointAcc"
    val find = "find"
    val instanceCounter = "_instanceCounter"
    val id = "_id"
    val removePrefix = "remove_"
    val addPrefix = "add_"
    val checkPrefix = "check_"
  }
}

class CheckRuntime private (program: IRGraph.Program) {
  import CheckRuntime.Names
  val ownedFields: IRGraph.StructDefinition =
    program.struct(Names.ownedFieldsStruct)
  val ownedFieldsRef = new IRGraph.ReferenceType(ownedFields)
  val ownedFieldInstanceCounter: StructField =
    ownedFields.fields.find(_.name == "instanceCounter").get
  val initOwnedFields: IRGraph.MethodDefinition =
    program.method(Names.initOwnedFields)
  val addStructAcc: IRGraph.MethodDefinition =
    program.method(Names.addStructAcc)
  val addAcc: IRGraph.MethodDefinition = program.method(Names.addAcc)
  val loseAcc: IRGraph.MethodDefinition = program.method(Names.loseAcc)
  val addDisjointAcc: IRGraph.MethodDefinition =
    program.method(Names.addDisjointAcc)
  val join: IRGraph.MethodDefinition = program.method(Names.join)
  val disjoin: IRGraph.MethodDefinition = program.method(Names.disjoin)
  val assertAcc: IRGraph.MethodDefinition = program.method(Names.assertAcc)
  val assertDisjointAcc: IRGraph.MethodDefinition =
    program.method(Names.assertDisjointAcc)
  val find: IRGraph.MethodDefinition = program.method(Names.find)
}
