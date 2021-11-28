package gvc.transformer
import viper.silver.{ast => vpr}
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import IRGraph._

object IRGraphSilver {
  def toSilver(program: IRGraph.Program) = new Converter(program).convert()

  class Converter(ir: IRGraph.Program) {
    private val RESULT = "$result"
    val fields = mutable.ListBuffer[vpr.Field]()
    val structFields = mutable.Map[StructField, vpr.Field]()

    def declareField(name: String, typ: vpr.Type): vpr.Field = {
      val field = vpr.Field("$refValue", vpr.Ref)()
      fields += field
      field
    }

    lazy val refPointer = declareField("$refValue", vpr.Ref)
    lazy val intPointer = declareField("$intValue", vpr.Int)
    lazy val boolPointer = declareField("$boolValue", vpr.Bool)

    def convert(): vpr.Program = {
      val predicates = ir.predicates.map(convertPredicate).toList
      val methods = ir.methods.map(convertMethod).toList
      val fields = this.fields.toSeq.sortBy(_.name).toList

      vpr.Program(Seq.empty, fields, Seq.empty, predicates, methods, Seq.empty)()
    }

    def convertMethod(method: Method): vpr.Method = {
      val params = method.parameters.map(convertDecl).toList
      val vars = method.variables.map(convertDecl).toList
      val ret = method.returnType.map({ ret => vpr.LocalVarDecl(RESULT, convertType(ret))() }).toSeq
      val pre = method.precondition.map(convertExpr).toSeq
      val post = method.postcondition.map(convertExpr).toSeq
      val body = ListBuffer[vpr.Stmt]()
      convertBlock(method.entry, body)

      vpr.Method(method.name, params, ret, pre, post, Some(vpr.Seqn(body, vars)()))()
    }

    def convertDecl(decl: Var): vpr.LocalVarDecl = {
      vpr.LocalVarDecl(decl.name, convertType(decl.valueType))()
    }

    def convertField(field: StructField): vpr.Field =
      structFields.getOrElseUpdate(field, vpr.Field(field.struct.name + "$" + field.name, convertType(field.valueType))())

    def convertType(t: Type) = t match {
      case _: ReferenceType => vpr.Ref
      case _: PointerType => vpr.Ref
      case IntType => vpr.Int
      case BoolType => vpr.Bool
      case CharType => vpr.Int
    }

    def getPointerField(t: Type) = t match {
      case _: ReferenceType | _: PointerType => refPointer
      case IntType | CharType => intPointer
      case BoolType => boolPointer
    }

    def getReturnVar(method: Method): vpr.LocalVar =
      vpr.LocalVar(RESULT, convertType(method.returnType.get))()

    def convertBlock(block: Block, output: ListBuffer[vpr.Stmt]): Unit = {
      block match {
        case basic: BasicBlock => {
          output ++= basic.ops.flatMap(convertOp)
        }

        case iff: IfBlock => {
          val ifTrue = ListBuffer[vpr.Stmt]()
          val ifFalse = ListBuffer[vpr.Stmt]()
          convertBlock(iff.ifTrue, ifTrue)
          convertBlock(iff.ifFalse, ifFalse)
          output += vpr.If(convertExpr(iff.condition), vpr.Seqn(ifTrue, Seq.empty)(), vpr.Seqn(ifFalse, Seq.empty)())()
        }

        case whil: WhileBlock => {
          val body = ListBuffer[vpr.Stmt]()
          convertBlock(whil.body, body)
          output += vpr.While(
            convertExpr(whil.condition),
            whil.invariant.map(convertExpr).toList,
            vpr.Seqn(body, Seq.empty)())()
        }
      }

      block.next match {
        case None => ()
        case Some(next) => convertBlock(next, output)
      }
    }

    def convertOp(op: Op): Seq[vpr.Stmt] = op match {
      case invoke: Invoke => {
        val target = invoke.target.map(convertVar)
        val args = invoke.arguments.map(convertExpr).toList
        Seq(vpr.MethodCall(invoke.method.name, args, target.toSeq)(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos))
      }

      case alloc: AllocValue => {
        val target = convertVar(alloc.target)
        val field = getPointerField(alloc.valueType)
        Seq(vpr.NewStmt(target, Seq(field))())
      }

      case alloc: AllocStruct => {
        val target = convertVar(alloc.target)
        val fields = alloc.struct.fields.map(convertField).toList
        Seq(vpr.NewStmt(target, fields)())
      }

      case assign: Assign =>
        Seq(vpr.LocalVarAssign(convertVar(assign.target), convertExpr(assign.value))())
      
      case assign: AssignMember =>
        Seq(vpr.FieldAssign(convertMember(assign.member), convertExpr(assign.value))())

      case assert: Assert => assert.method match {
        case AssertMethod.Imperative => Seq.empty
        case AssertMethod.Specification => Seq(vpr.Assert(convertExpr(assert.value))())
      }

      case fold: Fold => Seq(vpr.Fold(convertPredicateInstance(fold.instance))())
      case unfold: Unfold => Seq(vpr.Unfold(convertPredicateInstance(unfold.instance))())
      case error: Error => Seq(vpr.Assert(vpr.FalseLit()())())

      case ret: ReturnValue =>
          Seq(vpr.LocalVarAssign(getReturnVar(ret.method), convertExpr(ret.value))())
      case ret: ReturnInvoke =>
        Seq(vpr.MethodCall(
          ret.invoke.name,
          ret.arguments.map(convertExpr),
          Seq(getReturnVar(ret.method))
        )(vpr.NoPosition, vpr.NoInfo, vpr.NoTrafos))
      case _: Return => Seq.empty
    }

    def convertVar(v: Var): vpr.LocalVar =
      vpr.LocalVar(v.name, convertType(v.valueType))()

    def convertMember(member: Member): vpr.FieldAccess = member match {
      case member: FieldMember => vpr.FieldAccess(convertExpr(member.root), convertField(member.field))()
      case member: DereferenceMember => vpr.FieldAccess(convertExpr(member.root), getPointerField(member.valueType))()
    }

    def convertPredicateInstance(pred: PredicateInstance): vpr.PredicateAccessPredicate =
      vpr.PredicateAccessPredicate(vpr.PredicateAccess(pred.arguments.map(convertExpr), pred.predicate.name)(), vpr.FullPerm()())()

    def convertExpr(expr: Expression): vpr.Exp = expr match {
      case v: Var => convertVar(v)
      case m: Member => convertMember(m)
      case acc: Accessibility => vpr.FieldAccessPredicate(convertMember(acc.member), vpr.FullPerm()())()
      case pred: PredicateInstance => convertPredicateInstance(pred)
      case result: Result => getReturnVar(result.method)
      case imp: Imprecise => vpr.ImpreciseExp(imp.precise.map(convertExpr).getOrElse(vpr.TrueLit()()))()
      case int: Int => vpr.IntLit(BigInt(int.value))()
      case char: Char => vpr.IntLit(BigInt(char.value))()
      case bool: Bool => vpr.BoolLit(bool.value)()
      case n: Null => vpr.NullLit()()
      case cond: Conditional => vpr.CondExp(convertExpr(cond.condition), convertExpr(cond.ifTrue), convertExpr(cond.ifFalse))()
      case bin: Binary => {
        val left = convertExpr(bin.left)
        val right = convertExpr(bin.right)
        bin.operator match {
          case BinaryOp.Add => vpr.Add(left, right)()
          case BinaryOp.Subtract => vpr.Sub(left, right)()
          case BinaryOp.Divide => vpr.Div(left, right)()
          case BinaryOp.Multiply => vpr.Mul(left, right)()
          case BinaryOp.And => vpr.And(left, right)()
          case BinaryOp.Or => vpr.Or(left, right)()
          case BinaryOp.Equal => vpr.EqCmp(left, right)()
          case BinaryOp.NotEqual => vpr.NeCmp(left, right)()
          case BinaryOp.Less => vpr.LtCmp(left, right)()
          case BinaryOp.LessOrEqual => vpr.LeCmp(left, right)()
          case BinaryOp.Greater => vpr.GtCmp(left, right)()
          case BinaryOp.GreaterOrEqual => vpr.GeCmp(left, right)()
        }
      }

      case unary: Unary => {
        val value = convertExpr(unary.operand)
        unary.operator match {
          case UnaryOp.Negate => vpr.Minus(value)()
          case UnaryOp.Not => vpr.Not(value)()
        }
      }
    }

    def convertPredicate(pred: IRGraph.Predicate): vpr.Predicate = {
      vpr.Predicate(pred.name, pred.parameters.map(convertDecl).toList, Some(convertExpr(pred.expression)))()
    }
  }
}