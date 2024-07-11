package gvc.benchmarking

import gvc.transformer.IR
import gvc.weaver._
import gvc.weaver.CheckRuntime.Names
import gvc.transformer.IRPrinter

object BaselineChecks {
  def insert(
    program: IR.Program,
    checkFraming: Boolean = true,
    checkSpecs: Boolean = true
  ): Unit = {
    new BaselineChecks(program, checkFraming, checkSpecs).insert()
  }
}

class BaselineChecks(
  program: IR.Program,
  checkFraming: Boolean = true,
  checkSpecs: Boolean = true,
) {
  val structIds =
    program.structs.map(s => (s.name, s.addField("_id", IR.IntType))).toMap
  val runtime =
    CheckRuntime.addToIR(program)
  val impl = new CheckImplementation(program, runtime, structIds)
  val precision = new EquirecursivePrecision(program)

  def insert(): Unit = {
    program.methods.foreach(insertChecks)
    InstanceCounter.inject(program, structIds)
  }

  def insertChecks(
    method: IR.Method
  ): Unit = {
    val (callerPerms, perms) = {
      if (method.name == "main") {
        (None, method.addVar(impl.permsType, Names.primaryOwnedFields))
      } else {
        val permsArg =
          method.addParameter(impl.permsType, Names.primaryOwnedFields)
        if (precision.isPrecise(method.precondition))
          (Some(permsArg), method.addVar(impl.permsType, Names.temporaryOwnedFields))
        else
          (None, permsArg)
      }
    }

    insertChecks(method.body, perms, callerPerms)

    val initOps = callerPerms match {
      case Some(callerPerms) =>
        // Precise pre-condition
        impl.init(perms) ++
        (method.precondition match {
          case None => Seq.empty
          case Some(pre) =>
            // No need to use another temp set for separation
            checkSpecFraming(pre, callerPerms, ValueContext) ++
            impl.translate(
              pre,
              ValueContext,
              (if (checkSpecs) List(AssertMode(callerPerms)) else Nil) :::
                List(RemoveMode(callerPerms), AddMode(perms, guarded=true))
            )
        })
      case None =>
        // Imprecise pre-condition
        (if (method.name == "main") impl.init(perms) else Seq.empty) ++
        assertSpec(method.precondition, perms, method, ValueContext)
    }

    initOps ++=: method.body

    method.body ++= (method.body.lastOption match {
      case Some(_: IR.Return) =>
        Seq.empty // Handled when checking the `return` statement
      case _ =>
        postcondition(ValueContext, method, perms, callerPerms)
    })
  }

  def insertChecks(
    block: IR.Block,
    perms: IR.Var,
    callerPerms: Option[IR.Var]
  ): Unit = {
    var element = block.headOption
    while (element.isDefined) {
      val e = element.get
      // Get the next before the current element is removed, instructions are
      // added after it, etc.
      element = e.getNext
      insertChecks(e, perms, callerPerms)
    }
  }

  def insertChecks(
    op: IR.Op,
    perms: IR.Var,
    callerPerms: Option[IR.Var]
  ): Unit = op match {
    case alloc: IR.AllocStruct => {
      alloc.insertBefore(checkFraming(alloc.target, perms))
      alloc.insertAfter(impl.trackAllocation(alloc, perms))
    }

    case assert: IR.Assert if assert.kind == IR.AssertKind.Specification => {
      // We are assuming that expressions are self-framing
      if (checkSpecs) {
        val (baseMode, init) =
          if (SeparationChecks.canOverlap(assert.value)) {
            val tempPerms = assert.method.addVar(impl.permsType, Names.temporaryOwnedFields)
            (AddMode(tempPerms, guarded=true) :: Nil, impl.init(tempPerms))
          } else {
            (Nil, Seq.empty)
          }
        val checks = impl.translate(
          assert.value, ValueContext, AssertMode(perms) :: baseMode
        )

        assert.insertAfter(init ++ checks)
      }
      assert.remove()
    }

    case assert: IR.Assert => {
      // Imperative assert
      assert.insertBefore(checkFraming(assert.value, perms))
    }

    case assign: IR.Assign => {
      assign.insertBefore(
        checkFraming(assign.value, perms) ++
        checkFraming(assign.target, perms)
      )
    }

    case assign: IR.AssignMember => {
      assign.insertBefore(
        checkFraming(assign.member, perms) ++
        checkFraming(assign.value, perms)
      )
    }

    case error: IR.Error => {
      error.insertBefore(checkFraming(error.value, perms))
    }
    
    case fold: IR.Fold => {
      fold.remove()
    }

    case iff: IR.If => {
      iff.insertBefore(checkFraming(iff.condition, perms))
      insertChecks(iff.ifTrue, perms, callerPerms)
      insertChecks(iff.ifFalse, perms, callerPerms)
    }

    case invoke: IR.Invoke => {
      invoke.insertBefore(
        invoke.arguments.flatMap(checkFraming(_, perms)) ++
        invoke.target.map(checkFraming(_, perms)).getOrElse(Seq.empty)
      )
      invoke.callee match {
        case _: IR.Method =>
          invoke.arguments :+= perms
        case _ => ()
      }
      // Pre- and post-conditions handled inside the callee
    }

    case ret: IR.Return if ret.value.isDefined => {
      val value = ret.value.get
      ret.insertBefore(
        checkFraming(value, perms) ++
        postcondition(new ReturnContext(value), ret.method, perms, callerPerms)
      )
    }

    case ret: IR.Return =>
      throw new WeaverException("Invalid return")

    case unfold: IR.Unfold =>
      unfold.remove()

    case loop: IR.While => loop.invariant match {
      case imprecise: IR.Imprecise => {
        // Inherit the current permission set
        insertChecks(loop.body, perms, callerPerms)

        // Check loop invariant and framing of loop condition before the loop
        // and at the end of the loop body
        loop.insertBefore(
          checkFraming(loop.condition, perms, ValueContext) ++
          assertSpec(imprecise, perms, loop.method, ValueContext)
        )

        loop.body ++= checkFraming(loop.condition, perms, ValueContext)
        loop.body ++= assertSpec(imprecise, perms, loop.method, ValueContext)
      }
      case precise => {
        val method = loop.method

        val loopPerms = method.addVar(impl.permsType, Names.primaryOwnedFields)
        insertChecks(loop.body, loopPerms, callerPerms)

        // Create a new set of permissions and transfer invariant perms into it,
        // before the loop. This eliminates the need for another temp set for
        // separation checking.
        loop.insertBefore(
          checkFraming(loop.condition, perms, ValueContext) ++
          impl.init(loopPerms) ++
          impl.translate(
            precise,
            ValueContext,
            (if (checkSpecs) AssertMode(perms) :: Nil else Nil) :::
              RemoveMode(perms) :: AddMode(loopPerms) :: Nil
          )
        )

        // At the end of the loop, first check framing of loop condition
        loop.body ++= checkFraming(loop.condition, loopPerms, ValueContext)
        // Initialize a new temp set
        val newPerms = method.addVar(impl.permsType, Names.temporaryOwnedFields)
        loop.body ++= impl.init(newPerms)
        // Add invariant perms from the existing set to the new one
        // No need to remove since the existing set will be discarded
        loop.body ++= checkSpecFraming(precise, loopPerms, ValueContext)
        loop.body ++= impl.translate(
          precise,
          ValueContext,
          (if (checkSpecs) AssertMode(loopPerms) :: Nil else Nil) :::
            AddMode(newPerms) :: Nil
        )
        // Replace the existing set with the new one
        loop.body += new IR.Assign(loopPerms, newPerms)

        // After the loop ends, add the invariant perms back to the main set
        loop.insertAfter(
          impl.translate(precise, ValueContext, List(AddMode(perms)))
        )
      }
    }
  }

  def checkFraming(
    expr: IR.Expression,
    perms: IR.Expression,
    context: SpecificationContext = ValueContext
  ): Seq[IR.Op] = {
    if (checkFraming) {
      val check: IR.Expression => Seq[IR.Op] = checkFraming(_, perms, context)
      expr match {
        case bin: IR.Binary => bin.operator match {
          case IR.BinaryOp.And =>
            // Allow short-circuiting framing -- `false && x->y` does _not_
            // check `acc(x->y)`).
            check(bin.left) ++ makeIf(bin.left, check(bin.right))
          case IR.BinaryOp.Or =>
            check(bin.left) ++
            makeIf(new IR.Unary(IR.UnaryOp.Not, bin.left), check(bin.right))
          case _ =>
            check(bin.left) ++ check(bin.right)
        }
        case cond: IR.Conditional =>
          check(cond.condition) ++
          makeIf(cond.condition, check(cond.ifTrue), check(cond.ifFalse))
        case unary: IR.Unary =>
          check(unary.operand)
        case _: IR.Var | _: IR.Literal | _: IR.Result =>
          Seq.empty
        case field: IR.FieldMember =>
          impl.translateFieldPermission(field, List(AssertMode(perms)), context)
        case expr =>
          throw new WeaverException(
            "Unexpected expression '" + IRPrinter.print(expr) + "'")
      }
    } else {
      Seq.empty
    }
  }

  def checkSpecFraming(
    spec: IR.Expression,
    perms: IR.Expression,
    context: SpecificationContext
  ): Seq[IR.Op] = spec match {
    case imp: IR.Imprecise if imp.precise.isDefined =>
      checkSpecFramingInternal(imp.precise.get, perms, context)
    case _ => Seq.empty
  }

  def checkSpecFramingInternal(
    spec: IR.Expression,
    perms: IR.Expression,
    context: SpecificationContext
  ): Seq[IR.Op] = spec match {
    case imp: IR.Imprecise =>
      throw new WeaverException("Unexpected imprecise modifier")
    case acc: IR.Accessibility =>
      checkFraming(acc.member.root, perms, context)
    case bin: IR.Binary if bin.operator == IR.BinaryOp.And  =>
      checkSpecFramingInternal(bin.left, perms, context) ++
      checkSpecFramingInternal(bin.right, perms, context)
    case cond: IR.Conditional =>
      checkFraming(cond.condition, perms, context) ++
      makeIf(cond.condition,
        checkSpecFramingInternal(cond.ifTrue, perms, context),
        checkSpecFramingInternal(cond.ifFalse, perms, context))
    case pred: IR.PredicateInstance =>
      pred.arguments.flatMap(checkFraming(_, perms, context))
    case expr =>
      checkFraming(expr, perms, context)
  }

  def postcondition(
    context: SpecificationContext,
    method: IR.Method,
    perms: IR.Expression,
    callerPerms: Option[IR.Expression],
  ): Seq[IR.Op] = callerPerms match {
    case Some(callerPerms) => {
      // `calleePerms` is defined whenever the pre-condition is precise
      // Need to add the post-condition permissions back to `outerPerms`
      if (precision.isPrecise(method.postcondition)) {
        method.postcondition match {
          // No temporary set of perms is needed for separation since we are
          // adding them to the callee set
          case Some(post) if checkSpecs =>
            checkSpecFraming(post, perms, context) ++
            impl.translate(
              post,
              context,
              List(AssertMode(perms), AddMode(callerPerms, guarded=true))
            )
          case Some(post) =>
            checkSpecFraming(post, perms, context) ++
            impl.translate(
              post,
              context,
              List(AddMode(callerPerms, guarded=false))
            )
          case None => Seq.empty
        }
      } else {
        // Imprecise post-condition, so pass everything back
        assertSpec(method.postcondition, perms, method, context) ++
        impl.join(callerPerms, perms)
      }
    }
    case None => {
      // `calleePerms` is not defined, so the pre-condition is imprecise.
      // All permissions will be passed back since we are using the caller's
      // permissions already.
      assertSpec(method.postcondition, perms, method, context)
    }
  }

  def assertSpec(
    spec: IR.Expression,
    perms: IR.Expression,
    method: IR.Method,
    context: SpecificationContext = ValueContext,
  ): Seq[IR.Op] = {
    if (checkSpecs) {
      // Check if we need to add checks (and a corresponding temporary set of
      // permissions) for separation
      val framing = checkSpecFraming(spec, perms, context)
      val (mode, init) =
        if (SeparationChecks.canOverlap(spec)) {
          val tempPerms = method.addVar(impl.permsType, Names.temporaryOwnedFields)
          (AddMode(tempPerms, guarded=true) :: Nil, impl.init(tempPerms))
        } else {
          (Nil, Seq.empty)
        }
      val assert = impl.translate(spec, context, AssertMode(perms) :: mode)
      framing ++ init ++ assert
    } else {
      Seq.empty
    }
  }

  def assertSpec(
    spec: Option[IR.Expression],
    perms: IR.Expression,
    method: IR.Method,
    context: SpecificationContext
  ): Seq[IR.Op] = spec match {
    case None => Seq.empty
    case Some(spec) => assertSpec(spec, perms, method, context)
  }

  def makeIf(
    cond: IR.Expression,
    ifTrue: Seq[IR.Op],
    ifFalse: Seq[IR.Op] = Seq.empty
  ): Seq[IR.Op] = (ifTrue.isEmpty, ifFalse.isEmpty) match {
    case (true, true) => Seq.empty
    case (false, true) => {
      val iff = new IR.If(cond)
      iff.ifTrue ++= ifTrue
      Seq(iff)
    }
    case (true, false) => {
      val iff = new IR.If(new IR.Unary(IR.UnaryOp.Not, cond))
      iff.ifTrue ++= ifFalse
      Seq(iff)
    }
    case _ => {
      val iff = new IR.If(cond)
      iff.ifTrue ++= ifTrue
      iff.ifFalse ++= ifFalse
      Seq(iff)
    }
  }
}