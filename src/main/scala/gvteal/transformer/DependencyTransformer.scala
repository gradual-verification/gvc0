package gvc.transformer
import gvc.analyzer._

object DependencyTransformer {
  // TODO: There should be a *lot* more checking of the validity of definitions

  def transform(program: IR.Program, dependency: IR.Dependency, input: ResolvedProgram): Unit = {
    if (input.methodDefinitions.nonEmpty)
      throw new TransformerException("Cannot include method definitions in dependencies")
    
    def transformType(input: ResolvedType): IR.Type = input match {
      case UnknownType | NullType | VoidType => throw new TransformerException("Invalid type")
      case MissingNamedType(name) => throw new TransformerException(s"Missing type '$name'")
      case ResolvedStructType(structName) => throw new TransformerException(s"Invalid struct value type '$structName'")
      case ResolvedPointer(ResolvedStructType(structName)) => new IR.ReferenceType(program.struct(structName))
      case ResolvedPointer(valueType) => new IR.PointerType(transformType(valueType))
      case ResolvedArray(ResolvedStructType(structName)) => new IR.ReferenceArrayType(program.struct(structName))
      case ResolvedArray(valueType) => new IR.ArrayType(transformType(valueType))
      case IntType => IR.IntType
      case StringType => IR.StringType
      case CharType => IR.CharType
      case BoolType => IR.BoolType
    }

    input.structDefinitions
    .map(d => (d, dependency.defineStruct(d.name)))
    .foreach {
      case (input, defn) => {
        input.fields.foreach(field => defn.addField(field.name, transformType(field.valueType)))
      }
    }

    input.methodDeclarations
    .foreach(input => {
      val method = dependency.defineMethod(input.name, input.returnType match {
        case VoidType => None
        case t => Some(transformType(t))
      })

      if (isNonTrivial(input.precondition) || isNonTrivial(input.postcondition))
        throw new TransformerException("Specification in library declarations are not implemented")

      input.arguments.foreach(param => method.addParameter(param.name, transformType(param.valueType)))
    })
  }

  def isNonTrivial(spec: Option[ResolvedExpression]) =
    spec match {
      case None => false
      case Some(e: ResolvedBool) if e.value => false
      case _ => true
    }
}