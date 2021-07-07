package gvc.analyzer
import gvc.parser._
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.HashMap

case class ResolvedProgram(
  methodDeclarations: List[ResolvedMethodDeclaration],
  methodDefinitions: List[ResolvedMethodDefinition],
  structDefinitions: List[ResolvedStructDefinition],
  types: List[ResolvedTypeDef]
)

case class Scope(
  variables: Map[String, ResolvedVariable],
  methodDeclarations: Map[String, ResolvedMethodDeclaration],
  methodDefinitions: Map[String, ResolvedMethodDefinition],
  structDefinitions: Map[String, ResolvedStructDefinition],
  typeDefs: Map[String, ResolvedTypeDef],
  errors: ErrorSink
) {
  def defineStruct(struct: ResolvedStructDefinition): Scope = {
    if (structDefinitions.contains(struct.name)) {
      errors.error(struct.parsed, "'struct " + struct.name + "' is already defined")
      this
    } else {
      copy(structDefinitions = structDefinitions + (struct.name -> struct))
    }
  }

  def defineType(typeDef: ResolvedTypeDef): Scope = {
    if (typeDefs.contains(typeDef.name)) {
      errors.error(typeDef.parsed, "'" + typeDef.name + "' is already defined")
      this
    } else {
      if (methodDeclarations.contains(typeDef.name)) {
        // Log error but add to scope
        errors.error(typeDef.parsed, "Type name '" + typeDef.name + "' already used as a method")
      }

      copy(typeDefs = typeDefs + (typeDef.name -> typeDef))
    }
  }

  def declareMethod(method: ResolvedMethodDeclaration): Scope = {
    if (methodDeclarations.contains(method.name)) {
      this
    } else {
      copy(methodDeclarations = methodDeclarations + (method.name -> method))
    }
  }

  def defineMethod(method: ResolvedMethodDefinition): Scope = {
    if (methodDefinitions.contains(method.name)) {
      errors.error(method.parsed, "'" + method.name + "' is already defined")
      this
    } else {
      if (typeDefs.contains(method.name)) {
        // Log error but add to scope
        errors.error(method.parsed, "Method '" + method.name + "' already used as a type name")
      }
      copy(methodDefinitions = methodDefinitions + (method.name -> method))
    }
  }

  def declareVariable(variable: ResolvedVariable): Scope = {
    if (variables.contains(variable.name)) {
      errors.error(variable.parsed, "'" + variable.name + "' is already declared")
      this
    } else {
      // If it shadows a type name, log an error but add it to the scope to avoid
      // extra undeclared-variable errors
      if (typeDefs.contains(variable.name)) {
        errors.error(variable.parsed, "Type name '" + variable.name + "' used as a variable")
      }

      copy(variables = variables + (variable.name -> variable))
    }
  }

  def declareVariables(variables: Seq[ResolvedVariable]) = {
    // Add one-by-one to check for already defined variables
    variables.foldLeft(this) { _.declareVariable(_) }
  }
}

object Resolver {
  val reservedWords = Set(
    "int", "string", "char", "bool", "\result", "struct", "typedef"
  )

  def resolveType(input: Type, scope: Scope): ResolvedType = {
    input match {
      case ArrayType(valueType, _) => ResolvedArray(resolveType(valueType, scope))
      case PointerType(valueType, _) => ResolvedPointer(resolveType(valueType, scope))
      case NamedStructType(id, _) => resolveStruct(id, scope)
      case NamedType(id, _) => resolveNamedType(id, scope)
    }
  }

  def resolveStruct(id: Identifier, scope: Scope): ResolvedType = {
    // Structs may be used before they are declared or defined
    ResolvedStructType(id.name)
  }

  def resolveNamedType(id: Identifier, scope: Scope): ResolvedType = {
    val name = id.name
    BuiltinType.lookup.get(name) match {
      case Some(value) => value
      case None => scope.typeDefs.get(name) match {
        case Some(typeDef) => typeDef.actualType
        case None => {
          scope.errors.error(id, "Undefined type " + name)
          MissingNamedType(name)
        }
      }
    }
  }

  def resolveStructDefinition(input: StructDefinition, scope: Scope): ResolvedStructDefinition = {
    val fields = ListBuffer[ResolvedStructField]()
    for (field <- input.fields.get) {
      if (fields.exists(_.name == field.id.name)) {
        scope.errors.error(field, "Field '" + field.id.name + "' is already defined")
      }

      fields += ResolvedStructField(
        parsed = field,
        name = field.id.name,
        valueType = resolveType(field.valueType, scope)
      )
    }

    ResolvedStructDefinition(input, input.id.name, fields.toList)
  }

  def resolveTypeDef(input: TypeDefinition, scope: Scope): ResolvedTypeDef = {
    ResolvedTypeDef(
      parsed = input,
      name = input.id.name,
      actualType = resolveType(input.value, scope)
    )
  }

  def resolveStatement(input: Statement, scope: Scope): ResolvedStatement = {
    input match {
      // Variable defs are processed in resolveBlock
      case variable: VariableStatement => ???

      case expr: ExpressionStatement =>
        ResolvedExpressionStatement(
          parsed = expr,
          value = resolveExpression(expr.expression, scope)
        )

      case assign: AssignmentStatement =>
        ResolvedAssignment(
          parsed = assign,
          left = resolveExpression(assign.left, scope),
          value = resolveExpression(assign.right, scope),
          operation = convertAssignOp(assign, scope)
        )

      case unary: UnaryOperationStatement =>
        ResolvedIncrement(
          parsed = unary,
          value = resolveExpression(unary.value, scope),
          operation = unary.operator match {
            case UnaryOperator.Increment => IncrementOperation.Increment
            case UnaryOperator.Decrement => IncrementOperation.Decrement
            case _ => {
              scope.errors.error(unary, "Unsupported unary operation")
              IncrementOperation.Increment
            }
          }
        )

      case iff: IfStatement =>
        ResolvedIf(
          parsed = iff,
          condition = resolveExpression(iff.condition, scope),
          ifTrue = resolveScopedStatement(iff.then, scope),
          ifFalse = iff.els.map(resolveScopedStatement(_, scope))
        )
    
      case w: WhileStatement => {
        val (invariant, body) = resolveLoopInvariants(w.body, scope)
        ResolvedWhile(
          parsed = w,
          condition = resolveExpression(w.condition, scope),
          body = resolveScopedStatement(body, scope),
          invariant = invariant
        )
      }

      case f: ForStatement =>
        // Rewrite for into a while loop
        // For loops introduce their own scope, so wrap it all in a block
        // The spans get a little jumbled; for example, the incrementor is outside the block span
        resolveBlock(
          parsed = f,
          scope = scope,
          body = List(
            f.initializer,
            WhileStatement(
              condition = f.condition,
              span = f.span,
              specifications = List.empty,
              body = BlockStatement(
                // Move body specs to the while body so that loop invariants
                // are in the right place
                body = List(
                  f.body.withSpecifications(List.empty),
                  f.incrementor
                ),
                span = f.body.span,
                specifications = f.body.specifications,
                trailingSpecifications = List.empty
              )
            )
          ),
          specifications = f.specifications
        )

      case r: ReturnStatement =>
        ResolvedReturn(
          parsed = r,
          value = r.value.map(resolveExpression(_, scope))
        )
      
      case a: AssertStatement =>
        ResolvedAssert(a, resolveExpression(a.value, scope))

      case e: ErrorStatement =>
        ResolvedError(e, resolveExpression(e.value, scope))

      case b: BlockStatement => resolveBlock(b, scope, b.body)
    }
  }

  def convertAssignOp(stmt: AssignmentStatement, scope: Scope): Option[ArithmeticOperation] =
    stmt.operator match {
      case AssignOperator.Assign => None
      case AssignOperator.Add => Some(ArithmeticOperation.Add)
      case AssignOperator.Divide => Some(ArithmeticOperation.Divide)
      case AssignOperator.Multiply => Some(ArithmeticOperation.Multiply)
      case AssignOperator.Subtract => Some(ArithmeticOperation.Subtract)
      case _ => {
        scope.errors.error(stmt, "Unsupported assignment operator")
        None
      }
    }

  def resolveBlock(
    parsed: Statement,
    scope: Scope,
    body: List[Statement],
    specifications: List[Specification] = List.empty,
    trailingSpecifications: List[Specification] = List.empty
  ): ResolvedBlock = {
    var blockScope = scope
    var defs = ListBuffer[ResolvedVariable]()
    var resolved = ListBuffer[ResolvedStatement]()

    resolved ++= resolveSpecs(specifications, blockScope)

    for (stmt <- body) {
      resolved ++= resolveSpecs(stmt.specifications, blockScope)

      stmt match {
        case v: VariableStatement => {
          val varDef = ResolvedVariable(
            parsed = v,
            name = v.id.name,
            valueType = resolveType(v.valueType, scope))

          defs += varDef

          v.initialValue match {
            case None => ()
            case Some(value) => {
              resolved += ResolvedAssignment(
                parsed = v,
                left = ResolvedVariableRef(v.id, Some(varDef)),
                value = resolveExpression(value, blockScope),
                operation = None)
            }
          }
          
          blockScope = blockScope.declareVariable(varDef)
        }

        case _ => {
          resolved += resolveStatement(stmt, blockScope)
        }
      }
    }

    resolved ++= resolveSpecs(trailingSpecifications, blockScope)

    ResolvedBlock(
      parsed = parsed,
      variableDefs = defs.toList,
      statements = resolved.toList
    )
  }

  def resolveScopedStatement(input: Statement, scope: Scope): ResolvedBlock = {
    // Statements such as if and while introduce a transient scope. A variable definition
    // is valid, but it does not exist beyond that single statement. Moreover, specifications
    // can be added to any statement, which would generate multiple resolved statements.
    // Because we are handling all variable definitions at the block level, just rewrite the
    // single statement to always be a block statement.
    val (body, trailing) = input match {
      case block: BlockStatement => (block.body, block.trailingSpecifications)
      case _ => (List(input), List.empty)
    }

    resolveBlock(input, scope, body, input.specifications, trailing)
  }

  def resolveExpression(input: Expression, scope: Scope): ResolvedExpression = {
    input match {
      case variable: VariableExpression => resolveVariable(variable.variable, scope)

      case binary: BinaryExpression => {
        val left = resolveExpression(binary.left, scope)
        val right = resolveExpression(binary.right, scope)

        binary.operator match {
          case BinaryOperator.Add => ResolvedArithmetic(binary, left, right, ArithmeticOperation.Add)
          case BinaryOperator.Subtract => ResolvedArithmetic(binary, left, right, ArithmeticOperation.Subtract)
          case BinaryOperator.Divide => ResolvedArithmetic(binary, left, right, ArithmeticOperation.Divide)
          case BinaryOperator.Multiply => ResolvedArithmetic(binary, left, right, ArithmeticOperation.Multiply)
          case BinaryOperator.Equal => ResolvedComparison(binary, left, right, ComparisonOperation.EqualTo)
          case BinaryOperator.NotEqual => ResolvedComparison(binary, left, right, ComparisonOperation.NotEqualTo)
          case BinaryOperator.Greater => ResolvedComparison(binary, left, right, ComparisonOperation.GreaterThan)
          case BinaryOperator.GreaterEqual => ResolvedComparison(binary, left, right, ComparisonOperation.GreaterThanOrEqualTo)
          case BinaryOperator.Less => ResolvedComparison(binary, left, right, ComparisonOperation.LessThan)
          case BinaryOperator.LessEqual => ResolvedComparison(binary, left, right, ComparisonOperation.LessThanOrEqualTo)
          case BinaryOperator.LogicalAnd => ResolvedLogical(binary, left, right, LogicalOperation.And)
          case BinaryOperator.LogicalOr => ResolvedLogical(binary, left, right, LogicalOperation.Or)
          case _ => {
            // Log the error and return a mock that assumes add
            scope.errors.error(binary, "Unsupported operator " + binary.operator.toString())
            ResolvedArithmetic(binary, left, right, ArithmeticOperation.Add)
          }
        }
      }

      case unary: UnaryExpression => unary.operator match {
        case UnaryOperator.Not => ResolvedNot(unary, resolveExpression(unary.operand, scope))
        case UnaryOperator.Negate => ResolvedNegation(unary, resolveExpression(unary.operand, scope))
        case UnaryOperator.Deref => ResolvedDereference(unary, resolveExpression(unary.operand, scope))
        case op => {
          // Log the error and return the base expression
          scope.errors.error(unary, "Unsupported operator " + op.toString())
          resolveExpression(unary.operand, scope)
        }
      }
      
      case ternary: TernaryExpression =>
        ResolvedTernary(
          ternary,
          resolveExpression(ternary.condition, scope),
          resolveExpression(ternary.ifTrue, scope),
          resolveExpression(ternary.ifFalse, scope))

      case invoke: InvokeExpression => {
        val name = invoke.method.name

        val method =
          if (scope.variables.contains(name)) {
            scope.errors.error(invoke, "'" + name + "' is a variable, not a function")
            None
          } else {
            val decl = scope.methodDeclarations.get(name)
            if (!decl.isDefined) {
              scope.errors.error(invoke, "'" + name + "' is not declared")
            }
            decl
          }

        ResolvedInvoke(
          parsed = invoke,
          method = method,
          methodName = name,
          arguments = invoke.arguments.map(resolveExpression(_, scope)),
        )
      }

      case alloc: AllocExpression => {
        val valueType = resolveType(alloc.valueType, scope)
        verifyDefinedType(valueType, alloc, scope)
        ResolvedAlloc(alloc, valueType)
      }

      case alloc: AllocArrayExpression => {
        val valueType = resolveType(alloc.valueType, scope)
        verifyDefinedType(valueType, alloc, scope)
        ResolvedAllocArray(alloc, valueType, resolveExpression(alloc.length, scope))
      }

      case index: IndexExpression =>
        ResolvedArrayIndex(index, resolveExpression(index.parent, scope), resolveExpression(index.index, scope))

      case member: MemberExpression => {
        val parent = resolveExpression(member.parent, scope)
        val struct =
          if (member.isArrow) {
            parent.valueType match {
              case ResolvedPointer(ResolvedStructType(struct)) => Some(struct)
              case _ => {
                scope.errors.error(member, "Subject of '->' is not a pointer to a struct")
                None
              } 
            }
          } else {
            parent.valueType match {
              case ResolvedStructType(struct) => Some(struct)
              case _ => {
                scope.errors.error(member, "Subject of '.' is not a struct")
                None
              }
            }
          }

        val fieldName = member.field.name
        val field = struct match {
          case None => None

          case Some(struct) => scope.structDefinitions.get(struct) match {
            case None => {
              scope.errors.error(member, "'struct " + struct + "' is not defined")
              None
            }

            case Some(definition) => definition.fields.find(_.name == fieldName) match {
              case None => {
                scope.errors.error(member, "'" + fieldName + "' is not defined in '" + parent.valueType.toString())
                None
              }

              case Some(field) => Some(field)
            }
          }
        }

        ResolvedMember(
          parsed = member,
          parent = parent,
          field = field,
          fieldName = fieldName,
          isArrow = member.isArrow
        )
      }

      case string: StringExpression => ResolvedString(string)
      case char: CharacterExpression => ResolvedChar(char)
      case int: IntegerExpression => ResolvedInt(int)
      case bool: BooleanExpression => ResolvedBool(bool)
      case n: NullExpression => ResolvedNull(n)
    }
  }

  def resolveVariable(id: Identifier, scope: Scope): ResolvedExpression = {
    val variable = scope.variables.get(id.name)
    if (!variable.isDefined) {
      scope.errors.error(id, "'" + id.name + "' is not defined")
    }

    ResolvedVariableRef(id, variable)
  }

  def verifyDefinedType(t: ResolvedType, node: Node, scope: Scope): Unit = {
    t match {
      case ResolvedStructType(name) => {
        if (!scope.structDefinitions.contains(name)) {
          scope.errors.error(node, "'struct " + name + "' is not defined")
        }
      }

      case ResolvedPointer(valueType) => verifyDefinedType(valueType, node, scope)
      case ResolvedArray(valueType) => verifyDefinedType(valueType, node, scope)
      case _ => ()
    }
  }

  def resolveSpecs(specs: List[Specification], scope: Scope): Option[ResolvedAssert] = {
    val asserts = specs.flatMap({
      case assert: AssertSpecification => Some(resolveExpression(assert.value, scope))
      case other => {
        scope.errors.error(other, "Invalid specification")
        None
      }
    })

    asserts match {
      case head :: _ => Some(ResolvedAssert(head.parsed, combineBooleans(asserts).get))
      case _ => None
    }
  }

  def combineBooleans(expressions: Seq[ResolvedExpression]): Option[ResolvedExpression] = {
    expressions.foldLeft[Option[ResolvedExpression]](None)((current, expr) => {
      current match {
        case None => Some(expr)
        case Some(value) => Some(ResolvedLogical(
          parsed = expr.parsed,
          left = value,
          right = expr,
          operation = LogicalOperation.And
        ))
      }
    })
  }

  def resolveLoopInvariants(stmt: Statement, scope: Scope): (Option[ResolvedExpression], Statement) = {
    // Rewrite the loop body removing loop invariant specifications
    val loopInvariants = stmt.specifications.collect {
      case li: LoopInvariantSpecification => li
    }
    val invariant = combineBooleans(loopInvariants.map(spec => resolveExpression(spec.value, scope)))
    val otherSpecs = stmt.specifications.filterNot(_.isInstanceOf[LoopInvariantSpecification])
    (invariant, stmt.withSpecifications(otherSpecs))
  }

  def resolveMethodDeclaration(input: MethodDefinition, scope: Scope): ResolvedMethodDeclaration = {
    val retType = resolveType(input.returnType, scope)
    val parameters = input.arguments.map(arg => ResolvedVariable(arg, arg.id.name, resolveType(arg.valueType, scope)))

    // Parameters may be referenced in method specifications
    val specScope = scope.declareVariables(parameters)

    val preconditions = ListBuffer[ResolvedExpression]()
    val postconditions = ListBuffer[ResolvedExpression]()
    for (spec <- input.specifications) {
      spec match {
        case requires: RequiresSpecification => preconditions += resolveExpression(requires.value, specScope)
        case ensures: EnsuresSpecification => postconditions += resolveExpression(ensures.value, specScope)
        case invariant: LoopInvariantSpecification => {
          // TODO: Should invalid invariants be type-checked?
          resolveExpression(invariant.value, specScope) // To check for resolving errors
          scope.errors.error(invariant, "Invalid loop_invariant")
        }
        case assert: AssertSpecification => {
          // TODO: Should invalid asserts be type-checked?
          resolveExpression(assert.value, specScope) // To check for resolving errors
          scope.errors.error(assert, "Invalid assert")
        }
      }
    }

    ResolvedMethodDeclaration(
      parsed = input,
      name = input.id.name,
      returnType = retType,
      arguments = parameters,
      precondition = combineBooleans(preconditions.toSeq),
      postcondition = combineBooleans(postconditions.toSeq)
    )
  }

  def resolveMethodDefinition(input: MethodDefinition, localDecl: ResolvedMethodDeclaration, scope: Scope): ResolvedMethodDefinition = {
    // Add method parameters to variable scope
    val methodScope = scope.declareVariables(localDecl.arguments)

    val block = input.body.get
    val resolvedBlock = resolveBlock(
      parsed = block,
      scope = methodScope,
      body = block.body,
      specifications = block.specifications,
      trailingSpecifications = block.trailingSpecifications
    )

    val initialDecl = scope.methodDeclarations(input.id.name)
    ResolvedMethodDefinition(input, initialDecl, resolvedBlock)
  }

  def resolveProgram(program: List[Definition], errors: ErrorSink): ResolvedProgram = {
    val methodDeclarations = ListBuffer[ResolvedMethodDeclaration]()
    val methodDefinitions = ListBuffer[ResolvedMethodDefinition]()
    val structDefinitions = ListBuffer[ResolvedStructDefinition]()
    val types = ListBuffer[ResolvedTypeDef]()

    var scope = Scope(
      variables = Map.empty,
      methodDeclarations = Map.empty,
      methodDefinitions = Map.empty,
      structDefinitions = Map.empty,
      typeDefs = Map.empty,
      errors = errors
    )

    for (definition <- program) {
      definition match {
        // TODO: Implement use declarations
        case _: UseDeclaration => ???

        case t: TypeDefinition => {
          val typeDef = resolveTypeDef(t, scope)
          types += typeDef
          scope = scope.defineType(typeDef)
        }

        case s: StructDefinition => {
          if (s.fields.isDefined) {
            val definition = resolveStructDefinition(s, scope)
            structDefinitions += definition
            scope = scope.defineStruct(definition)
          }
        }

        case m: MethodDefinition => {
          val decl = resolveMethodDeclaration(m, scope)
          methodDeclarations += decl
          if (!scope.methodDeclarations.contains(decl.name)) {
            scope = scope.copy(methodDeclarations = scope.methodDeclarations + (decl.name -> decl))
          }

          if (m.body.isDefined) {
            val definition = resolveMethodDefinition(m, decl, scope)
            methodDefinitions += definition
            scope = scope.defineMethod(definition)
          }
        }
      }
    }

    ResolvedProgram(
      methodDeclarations = methodDeclarations.toList,
      methodDefinitions = methodDefinitions.toList,
      structDefinitions = structDefinitions.toList,
      types = types.toList
    )
  }
}