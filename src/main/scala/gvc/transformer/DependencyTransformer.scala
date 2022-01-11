package gvc.transformer
import gvc.analyzer._

object DependencyTransformer {
  // TODO: There should be a *lot* more checking of the validity of definitions

  def transform(program: IRGraph.Program, dependency: IRGraph.Dependency, input: ResolvedProgram): Unit = {
    if (input.methodDefinitions.nonEmpty)
      throw new TransformerException("Cannot include method definitions in dependencies")
    
    def transformType(input: ResolvedType): IRGraph.Type = input match {
      case UnknownType | NullType | VoidType => throw new TransformerException("Invalid type")
      case MissingNamedType(name) => throw new TransformerException(s"Missing type '$name'")
      case ResolvedStructType(structName) => throw new TransformerException(s"Invalid struct value type '$structName'")
      case ResolvedPointer(ResolvedStructType(structName)) => new IRGraph.ReferenceType(program.struct(structName))
      case ResolvedPointer(valueType) => new IRGraph.PointerType(transformType(valueType))
      case ResolvedArray(ResolvedStructType(structName)) => new IRGraph.ReferenceArrayType(program.struct(structName))
      case ResolvedArray(valueType) => new IRGraph.ArrayType(transformType(valueType))
      case IntType => IRGraph.IntType
      case StringType => IRGraph.StringType
      case CharType => IRGraph.CharType
      case BoolType => IRGraph.BoolType
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

      input.arguments.foreach(param => method.addParameter(param.name, transformType(param.valueType)))
    })
  }
}