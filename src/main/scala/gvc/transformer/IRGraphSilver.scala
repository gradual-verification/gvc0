package gvc.transformer
import viper.silver.{ast => vpr}
import scala.collection.mutable
import IRGraph._

case class SilverVarId(methodName: java.lang.String, varName: java.lang.String)

class SilverProgram(
  val program: vpr.Program,

  // Map of (methodName, varName) Silver variables that represent the result
  // of the invoke
  val temporaryVars: Map[SilverVarId, IRGraph.Invoke]
)

object IRGraphSilver {
  def toSilver(program: IRGraph.Program) = new Converter(program).convert()

  object Names {
    val ResultVar = "$result"
    val RefPointerValue = "$refValue"
    val IntPointerValue = "$intValue"
    val BoolPointerValue = "$boolValue"
  }

  private class TempVars(methodName: java.lang.String, index: mutable.Map[SilverVarId, Invoke]) {
    private var counter = -1
    val declarations = mutable.ListBuffer[vpr.LocalVarDecl]()

    def next(invoke: Invoke, t: vpr.Type): vpr.LocalVar = {
      counter += 1
      val name = "$result_" + counter

      index += SilverVarId(methodName, name) -> invoke

      val decl = vpr.LocalVarDecl(name, t)()
      declarations += decl
      decl.localVar
    }
  }

  class Converter(ir: IRGraph.Program) {
    val fields = mutable.ListBuffer[vpr.Field]()
    val structFields = mutable.Map[StructField, vpr.Field]()

    def declareField(name: scala.Predef.String, typ: vpr.Type): vpr.Field = {
      val field = vpr.Field(name, typ)()
      fields += field
      field
    }

    lazy val refPointer = declareField(Names.RefPointerValue, vpr.Ref)
    lazy val intPointer = declareField(Names.IntPointerValue, vpr.Int)
    lazy val boolPointer = declareField(Names.BoolPointerValue, vpr.Bool)

    def convert(): SilverProgram = {
      val predicates = ir.predicates.map(convertPredicate).toList
      val tempVarIndex = mutable.Map[SilverVarId, Invoke]()
      val methods = ir.methods.map(convertMethod(_, tempVarIndex)).toList
      val fields = this.fields.toSeq.sortBy(_.name).toList

      val program = vpr.Program(
        Seq.empty,
        fields,
        Seq.empty,
        predicates,
        methods,
        Seq.empty
      )()

      new SilverProgram(program, tempVarIndex.toMap)
    }

    private def convertMethod(method: Method, tempVarIndex: mutable.Map[SilverVarId, Invoke]): vpr.Method = {
      var tempCount = 0

      val params = method.parameters.map(convertDecl).toList
      val vars = method.variables.map(convertDecl).toList
      val ret = method.returnType
        .map({ ret => vpr.LocalVarDecl(Names.ResultVar, convertType(ret))() })
        .toSeq
      val pre = method.precondition.map(convertExpr).toSeq
      val post = method.postcondition.map(convertExpr).toSeq
      val tempVars = new TempVars(method.name, tempVarIndex)
      val body = method.body.flatMap(convertOp(_, tempVars)).toList
      val decls = vars ++ tempVars.declarations.toList

      vpr.Method(
        method.name,
        params,
        ret,
        pre,
        post,
        Some(vpr.Seqn(body, decls)())
      )()
    }

    def convertDecl(decl: Var): vpr.LocalVarDecl = {
      vpr.LocalVarDecl(decl.name, convertType(decl.varType))()
    }

    def convertField(field: StructField): vpr.Field =
      structFields.getOrElseUpdate(
        field,
        declareField(
          field.struct.name + "$" + field.name,
          convertType(field.valueType)
        )
      )

    def convertType(t: Type) = t match {
      case _: ReferenceType => vpr.Ref
      case _: PointerType   => vpr.Ref
      case IntType          => vpr.Int
      case BoolType         => vpr.Bool
      case CharType         => vpr.Int
      case _                => throw new IRException(s"Unsupported type: ${t.name}")
    }

    def getPointerField(t: Type) = t match {
      case _: ReferenceType | _: PointerType => refPointer
      case IntType | CharType                => intPointer
      case BoolType                          => boolPointer
      case _                                 => throw new IRException(s"Unsupported type: ${t.name}")
    }

    def getReturnVar(method: Method): vpr.LocalVar =
      vpr.LocalVar(Names.ResultVar, convertType(method.returnType.get))()

    private def convertOp(op: Op, tempVars: TempVars): Seq[vpr.Stmt] = op match {
      case iff: If => {
        val ifTrue = iff.ifTrue.flatMap(convertOp(_, tempVars)).toList
        val ifFalse = iff.ifFalse.flatMap(convertOp(_, tempVars)).toList
        Seq(
          vpr.If(
            convertExpr(iff.condition),
            vpr.Seqn(ifTrue, Seq.empty)(),
            vpr.Seqn(ifFalse, Seq.empty)()
          )()
        )
      }

      case loop: While => {
        Seq(
          vpr.While(
            convertExpr(loop.condition),
            List(convertExpr(loop.invariant)),
            vpr.Seqn(loop.body.flatMap(convertOp(_, tempVars)).toList, Seq.empty)()
          )()
        )
      }

      case invoke: Invoke => {
        val target: Option[vpr.LocalVar] = invoke.target match {
          case Some(v: Var) => Some(convertVar(v))
          case Some(_) =>
            throw new IRException(
              "Complex invoke target cannot be converted to Silver"
            )
          
          case None => invoke.callee.returnType match {
            case Some(retType) =>
              Some(tempVars.next(invoke, convertType(retType)))
            case None =>
              None
          }
        }

        val args = invoke.arguments.map(convertExpr).toList
        Seq(
          vpr.MethodCall(invoke.callee.name, args, target.toSeq)(
            vpr.NoPosition,
            vpr.NoInfo,
            vpr.NoTrafos
          )
        )
      }

      case alloc: AllocValue => {
        val target = convertVar(alloc.target)
        val field = getPointerField(alloc.valueType)
        Seq(vpr.NewStmt(target, Seq(field))())
      }

      case alloc: AllocStruct => {
        val target = alloc.target match {
          case v: Var => convertVar(v)
          case _ =>
            throw new IRException(
              "Complex alloc target cannot be converted to Silver"
            )
        }
        val fields = alloc.struct.fields.map(convertField).toList
        Seq(vpr.NewStmt(target, fields)())
      }

      case _: AllocArray =>
        throw new IRException("Array operations are not implemented in Silver")

      case assign: Assign =>
        Seq(
          vpr.LocalVarAssign(
            convertVar(assign.target),
            convertExpr(assign.value)
          )()
        )

      case assign: AssignMember =>
        Seq(
          vpr.FieldAssign(
            convertMember(assign.member),
            convertExpr(assign.value)
          )()
        )

      case assert: Assert =>
        assert.kind match {
          case AssertKind.Imperative => Seq.empty
          case AssertKind.Specification =>
            Seq(vpr.Assert(convertExpr(assert.value))())
        }

      case fold: Fold =>
        Seq(vpr.Fold(convertPredicateInstance(fold.instance))())
      case unfold: Unfold =>
        Seq(vpr.Unfold(convertPredicateInstance(unfold.instance))())
      case error: Error => Seq(vpr.Assert(vpr.FalseLit()())())

      case ret: Return =>
        ret.value match {
          case None => Seq.empty
          case Some(value) =>
            Seq(
              vpr.LocalVarAssign(getReturnVar(ret.method), convertExpr(value))()
            )
        }
    }

    def convertVar(v: Var): vpr.LocalVar =
      vpr.LocalVar(v.name, convertType(v.varType))()

    def convertMember(member: Member): vpr.FieldAccess = member match {
      case member: FieldMember =>
        vpr.FieldAccess(convertExpr(member.root), convertField(member.field))()
      case member: DereferenceMember =>
        vpr.FieldAccess(
          convertExpr(member.root),
          getPointerField(
            member.valueType.getOrElse(
              throw new IRException("Invalid dereference")
            )
          )
        )()
      case _: ArrayMember =>
        throw new IRException("Array operations are not implemented in Silver")
    }

    def convertPredicateInstance(
        pred: PredicateInstance
    ): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          pred.arguments.map(convertExpr),
          pred.predicate.name
        )(),
        vpr.FullPerm()()
      )()

    def convertExpr(expr: Expression): vpr.Exp = expr match {
      case v: Var    => convertVar(v)
      case m: Member => convertMember(m)
      case acc: Accessibility =>
        vpr.FieldAccessPredicate(convertMember(acc.member), vpr.FullPerm()())()
      case pred: PredicateInstance => convertPredicateInstance(pred)
      case result: Result          => getReturnVar(result.method)
      case imp: Imprecise =>
        vpr.ImpreciseExp(
          imp.precise.map(convertExpr).getOrElse(vpr.TrueLit()())
        )()
      case int: Int    => vpr.IntLit(BigInt(int.value))()
      case char: Char  => vpr.IntLit(BigInt(char.value))()
      case bool: Bool  => vpr.BoolLit(bool.value)()
      case str: String => throw new IRException("Strings are not supported.")
      case n: Null     => vpr.NullLit()()
      case cond: Conditional =>
        vpr.CondExp(
          convertExpr(cond.condition),
          convertExpr(cond.ifTrue),
          convertExpr(cond.ifFalse)
        )()
      case bin: Binary => {
        val left = convertExpr(bin.left)
        val right = convertExpr(bin.right)
        bin.operator match {
          case BinaryOp.Add            => vpr.Add(left, right)()
          case BinaryOp.Subtract       => vpr.Sub(left, right)()
          case BinaryOp.Divide         => vpr.Div(left, right)()
          case BinaryOp.Multiply       => vpr.Mul(left, right)()
          case BinaryOp.And            => vpr.And(left, right)()
          case BinaryOp.Or             => vpr.Or(left, right)()
          case BinaryOp.Equal          => vpr.EqCmp(left, right)()
          case BinaryOp.NotEqual       => vpr.NeCmp(left, right)()
          case BinaryOp.Less           => vpr.LtCmp(left, right)()
          case BinaryOp.LessOrEqual    => vpr.LeCmp(left, right)()
          case BinaryOp.Greater        => vpr.GtCmp(left, right)()
          case BinaryOp.GreaterOrEqual => vpr.GeCmp(left, right)()
        }
      }

      case unary: Unary => {
        val value = convertExpr(unary.operand)
        unary.operator match {
          case UnaryOp.Negate => vpr.Minus(value)()
          case UnaryOp.Not    => vpr.Not(value)()
        }
      }
    }

    def convertPredicate(pred: IRGraph.Predicate): vpr.Predicate = {
      vpr.Predicate(
        pred.name,
        pred.parameters.map(convertDecl).toList,
        Some(convertExpr(pred.expression))
      )()
    }
  }
}
