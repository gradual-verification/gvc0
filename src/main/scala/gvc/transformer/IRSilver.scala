package gvc.transformer
import viper.silver.{ast => vpr}
import scala.collection.mutable

case class SilverVarId(methodName: String, varName: String)

object IRSilver {
  def toSilver(program: IR.Program) = new Converter(program).convert()

  object Names {
    val ReturnVar = "$result"
    val ReservedResult = "result"
    val RenamedResult = "_result$"
  }

  class Converter(ir: IR.Program) {
    val fields = mutable.ListBuffer[vpr.Field]()
    val structFields = mutable.Map[IR.StructField, vpr.Field]()

    def declareField(name: String, typ: vpr.Type): vpr.Field = {
      val field = vpr.Field(name, typ)()
      fields += field
      field
    }

    def convert(): vpr.Program = {
      val predicates = ir.predicates.map(convertPredicate).toList
      val methods = (
        ir.methods.map(convertMethod) ++
        ir.dependencies.flatMap(_.methods.map(convertLibraryMethod))
      ).toList
      val fields = this.fields.toSeq.sortBy(_.name).toList

      val program = vpr.Program(
        Seq.empty,
        fields,
        Seq.empty,
        predicates,
        methods,
        Seq.empty
      )()

      program
    }

    private def returnVarDecl(t: Option[IR.Type]): List[vpr.LocalVarDecl] = {
      t.map({ ret => vpr.LocalVarDecl(Names.ReturnVar, convertType(ret))() })
        .toList
    }

    private def convertLibraryMethod(method: IR.DependencyMethod): vpr.Method = {
      val retVar = returnVarDecl(method.returnType)
      val body = vpr.Seqn(
        method.returnType.map(r =>
          vpr.LocalVarAssign(retVar.head.localVar, convertExpr(r.default))()).toSeq,
        Seq.empty
      )()

      vpr.Method(
        method.name,
        method.parameters.map(convertDecl).toList,
        retVar,
        Seq.empty,
        Seq.empty,
        Some(body)
      )()
    }

    private def convertMethod(method: IR.Method): vpr.Method = {

      val params = method.parameters.map(convertDecl).toList
      val decls = method.variables.map(convertDecl).toList
      val ret = returnVarDecl(method.returnType)
      val pre = method.precondition.map(convertExpr).toSeq
      val post = method.postcondition.map(convertExpr).toSeq
      val body = method.body.flatMap(convertOp).toList

      vpr.Method(
        method.name,
        params,
        ret,
        pre,
        post,
        Some(vpr.Seqn(body, decls)())
      )()
    }

    def convertDecl(decl: IR.Var): vpr.LocalVarDecl = {
      vpr.LocalVarDecl(varName(decl.name), convertType(decl.varType))()
    }

    def convertField(field: IR.StructField): vpr.Field =
      structFields.getOrElseUpdate(
        field,
        declareField(
          field.struct.name + "$" + field.name,
          convertType(field.valueType)
        )
      )

    def convertType(t: IR.Type) = t match {
      case _: IR.ReferenceType => vpr.Ref
      case _: IR.PointerType   => vpr.Ref
      case IR.IntType          => vpr.Int
      case IR.BoolType         => vpr.Bool
      case IR.CharType         => vpr.Int
      case _                => throw new IRException(s"Unsupported type: ${t.name}")
    }

    def getReturnVar(method: IR.Method): vpr.LocalVar =
      vpr.LocalVar(Names.ReturnVar, convertType(method.returnType.get))()

    private def convertOp(op: IR.Op): Seq[vpr.Stmt] = op match {
      case iff: IR.If => {
        val ifTrue = iff.ifTrue.flatMap(convertOp).toList
        val ifFalse = iff.ifFalse.flatMap(convertOp).toList
        Seq(
          vpr.If(
            convertExpr(iff.condition),
            vpr.Seqn(ifTrue, Seq.empty)(),
            vpr.Seqn(ifFalse, Seq.empty)()
          )()
        )
      }

      case loop: IR.While => {
        Seq(
          vpr.While(
            convertExpr(loop.condition),
            List(convertExpr(loop.invariant)),
            vpr.Seqn(loop.body.flatMap(convertOp).toList, Seq.empty)()
          )()
        )
      }

      case invoke: IR.Invoke => {
        val target: Option[vpr.LocalVar] = invoke.target match {
          case Some(v: IR.Var) => Some(convertVar(v))
          case Some(_) =>
            throw new IRException(
              "Complex invoke target cannot be converted to Silver"
            )
          
          case None => invoke.callee.returnType match {
            case Some(retType) =>
              throw new IRException("Cannot convert invoke of non-void method with no target")
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

      case alloc: IR.AllocValue => {
        throw new IRException("Bare pointers cannot be converted")
      }

      case alloc: IR.AllocStruct => {
        val target = alloc.target match {
          case v: IR.Var => convertVar(v)
          case _ =>
            throw new IRException(
              "Complex alloc target cannot be converted to Silver"
            )
        }
        val fields = alloc.struct.fields.map(convertField).toList
        Seq(vpr.NewStmt(target, fields)())
      }

      case _: IR.AllocArray =>
        throw new IRException("Array operations are not implemented in Silver")

      case assign: IR.Assign =>
        Seq(
          vpr.LocalVarAssign(
            convertVar(assign.target),
            convertExpr(assign.value)
          )()
        )

      case assign: IR.AssignMember =>
        Seq(
          vpr.FieldAssign(
            convertMember(assign.member),
            convertExpr(assign.value)
          )()
        )

      case assert: IR.Assert =>
        assert.kind match {
          case IR.AssertKind.Imperative => Seq.empty
          case IR.AssertKind.Specification =>
            Seq(vpr.Assert(convertExpr(assert.value))())
        }

      case fold: IR.Fold =>
        Seq(vpr.Fold(convertPredicateInstance(fold.instance))())
      case unfold: IR.Unfold =>
        Seq(vpr.Unfold(convertPredicateInstance(unfold.instance))())
      case error: IR.Error => Seq(vpr.Assert(vpr.FalseLit()())())

      case ret: IR.Return =>
        ret.value match {
          case None => Seq.empty
          case Some(value) =>
            Seq(
              vpr.LocalVarAssign(getReturnVar(ret.method), convertExpr(value))()
            )
        }
    }

    def varName(name: String) = name match {
      case Names.ReservedResult => Names.RenamedResult
      case n => n
    }

    def convertVar(v: IR.Var): vpr.LocalVar = {
      vpr.LocalVar(varName(v.name), convertType(v.varType))()
    }

    def convertMember(member: IR.Member): vpr.FieldAccess = member match {
      case member: IR.FieldMember =>
        vpr.FieldAccess(convertExpr(member.root), convertField(member.field))()
      case member: IR.DereferenceMember =>
        throw new IRException("Bare pointers cannot be converted")
      case _: IR.ArrayMember =>
        throw new IRException("Array operations are not implemented in Silver")
    }

    def convertPredicateInstance(
        pred: IR.PredicateInstance
    ): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(
        vpr.PredicateAccess(
          pred.arguments.map(convertExpr),
          pred.predicate.name
        )(),
        vpr.FullPerm()()
      )()

    def convertExpr(expr: IR.Expression): vpr.Exp = expr match {
      case v: IR.Var    => convertVar(v)
      case m: IR.Member => convertMember(m)
      case acc: IR.Accessibility =>
        vpr.FieldAccessPredicate(convertMember(acc.member), vpr.FullPerm()())()
      case pred: IR.PredicateInstance => convertPredicateInstance(pred)
      case result: IR.Result          => getReturnVar(result.method)
      case imp: IR.Imprecise =>
        vpr.ImpreciseExp(
          imp.precise.map(convertExpr).getOrElse(vpr.TrueLit()())
        )()
      case int: IR.IntLit    => vpr.IntLit(BigInt(int.value))()
      case char: IR.CharLit  => vpr.IntLit(BigInt(char.value))()
      case bool: IR.BoolLit  => vpr.BoolLit(bool.value)()
      case str: IR.StringLit => throw new IRException("Strings are not supported.")
      case n: IR.NullLit     => vpr.NullLit()()
      case cond: IR.Conditional =>
        vpr.CondExp(
          convertExpr(cond.condition),
          convertExpr(cond.ifTrue),
          convertExpr(cond.ifFalse)
        )()
      case bin: IR.Binary => {
        val left = convertExpr(bin.left)
        val right = convertExpr(bin.right)
        bin.operator match {
          case IR.BinaryOp.Add            => vpr.Add(left, right)()
          case IR.BinaryOp.Subtract       => vpr.Sub(left, right)()
          case IR.BinaryOp.Divide         => vpr.Div(left, right)()
          case IR.BinaryOp.Multiply       => vpr.Mul(left, right)()
          case IR.BinaryOp.And            => vpr.And(left, right)()
          case IR.BinaryOp.Or             => vpr.Or(left, right)()
          case IR.BinaryOp.Equal          => vpr.EqCmp(left, right)()
          case IR.BinaryOp.NotEqual       => vpr.NeCmp(left, right)()
          case IR.BinaryOp.Less           => vpr.LtCmp(left, right)()
          case IR.BinaryOp.LessOrEqual    => vpr.LeCmp(left, right)()
          case IR.BinaryOp.Greater        => vpr.GtCmp(left, right)()
          case IR.BinaryOp.GreaterOrEqual => vpr.GeCmp(left, right)()
        }
      }

      case unary: IR.Unary => {
        val value = convertExpr(unary.operand)
        unary.operator match {
          case IR.UnaryOp.Negate => vpr.Minus(value)()
          case IR.UnaryOp.Not    => vpr.Not(value)()
        }
      }
    }

    def convertPredicate(pred: IR.Predicate): vpr.Predicate = {
      vpr.Predicate(
        pred.name,
        pred.parameters.map(convertDecl).toList,
        Some(convertExpr(pred.expression))
      )()
    }
  }
}
