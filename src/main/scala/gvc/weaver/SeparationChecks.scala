package gvc.weaver

// TODO: Factor this out
  // def traversePermissions(
  //     spec: IR.Expression,
  //     arguments: Option[Map[IR.Parameter, CheckExpression]],
  //     condition: Option[CheckExpression],
  //     checkType: CheckType
  // ): Seq[CheckInfo] = spec match {
  //   // Imprecise expressions just needs the precise part checked.
  //   // TODO: This should also enable framing checks.
  //   case imp: IR.Imprecise => {
  //     imp.precise.toSeq.flatMap(
  //       traversePermissions(_, arguments, condition, checkType)
  //     )
  //   }

  //   // And expressions just traverses both parts
  //   case and: IR.Binary if and.operator == IR.BinaryOp.And => {
  //     val left = traversePermissions(and.left, arguments, condition, checkType)
  //     val right =
  //       traversePermissions(and.right, arguments, condition, checkType)
  //     left ++ right
  //   }

  //   // A condition expression traverses each side with its respective condition, joined with the
  //   // existing condition if provided to support nested conditionals.
  //   case cond: IR.Conditional => {
  //     val baseCond = resolveValue(cond.condition, arguments)
  //     val negCond = CheckExpression.Not(baseCond)
  //     val (trueCond, falseCond) = condition match {
  //       case None => (baseCond, negCond)
  //       case Some(otherCond) =>
  //         (
  //           CheckExpression.And(otherCond, baseCond),
  //           CheckExpression.And(otherCond, negCond)
  //         )
  //     }

  //     val truePerms =
  //       traversePermissions(cond.ifTrue, arguments, Some(trueCond), checkType)
  //     val falsePerms = traversePermissions(
  //       cond.ifFalse,
  //       arguments,
  //       Some(falseCond),
  //       checkType
  //     )
  //     truePerms ++ falsePerms
  //   }

  //   // A single accessibility check
  //   case acc: IR.Accessibility => {
  //     val field = resolveValue(acc.member, arguments) match {
  //       case f: CheckExpression.Field => f
  //       case invalid =>
  //         throw new WeaverException(s"Invalid acc() argument: '$invalid'")
  //     }

  //     checkType match {
  //       case Separation =>
  //         Seq(
  //           CheckInfo(
  //             FieldSeparationCheck(field),
  //             condition.map(ImmediateCondition)
  //           )
  //         )
  //       case Verification =>
  //         Seq(
  //           CheckInfo(
  //             FieldAccessibilityCheck(field),
  //             condition.map(ImmediateCondition)
  //           )
  //         )
  //     }

  //   }
  //   case pred: IR.PredicateInstance => {
  //     checkType match {
  //       case Separation =>
  //         Seq(
  //           CheckInfo(
  //             PredicateSeparationCheck(
  //               pred.predicate.name,
  //               pred.arguments.map(resolveValue(_, arguments))
  //             ),
  //             condition.map(ImmediateCondition)
  //           )
  //         )
  //       case Verification =>
  //         Seq(
  //           CheckInfo(
  //             PredicateAccessibilityCheck(
  //               pred.predicate.name,
  //               pred.arguments.map(resolveValue(_, arguments))
  //             ),
  //             condition.map(ImmediateCondition)
  //           )
  //         )
  //     }

  //   }
  //   case _ => {
  //     // Otherwise there can be no permission specifiers in this term or its children
  //     Seq.empty
  //   }
  // }





  // Traverse the specifications for statements that require full permission checks
    // for (location <- needsSeparationChecking) {
    //   val (spec, arguments) = location match {
    //     case at: AtOp =>
    //       at.op match {
    //         case op: IR.Invoke =>
    //           op.callee match {
    //             case callee: IR.Method if callee.precondition.isDefined =>
    //               (
    //                 callee.precondition.get,
    //                 Some(
    //                   op.callee.parameters
    //                     .zip(op.arguments.map(resolveValue(_)))
    //                     .toMap
    //                 )
    //               )
    //             case _ =>
    //               throw new WeaverException(
    //                 s"Could not locate specification at invoke: $location")
    //           }
    //         case op: IR.Fold =>
    //           (
    //             op.instance.predicate.expression,
    //             Some(
    //               op.instance.predicate.parameters
    //                 .zip(op.instance.arguments.map(resolveValue(_)))
    //                 .toMap
    //             )
    //           )
    //         case op: IR.While  => (op.invariant, None)
    //         case op: IR.Assert => (op.value, None)
    //         case _ =>
    //           throw new WeaverException(
    //             "Could not locate specification for permission checking: " + location
    //               .toString()
    //           )
    //       }
    //     case MethodPost if irMethod.postcondition.isDefined =>
    //       (irMethod.postcondition.get, None)
    //     case _ =>
    //       throw new WeaverException(
    //         "Could not locate specification for permission checking: " + location
    //           .toString()
    //       )
    //   }

    //   val separationChecks =
    //     traversePermissions(spec, arguments, None, Separation).map(info =>
    //       RuntimeCheck(location, info.check, info.when))

    //   // Since the checks are for separation, only include them if there is more than one
    //   // otherwise, there can be no overlap
    //   val needsSeparationCheck =
    //     separationChecks match {
    //       case RuntimeCheck(_, _: FieldSeparationCheck, _) :: Nil => false
    //       case _ => true
    //     }
    //   if (needsSeparationCheck) {
    //     collectedChecks ++= separationChecks
    //   }
    // }



/* // Changes an expression from an IR expression into a CheckExpression. If an argument lookup
  // mapping is given, it will use this mapping to resolve variables. Otherwise, it will assume
  // any variables are accessible in the current scope.
  def resolveValue(
      input: IR.Expression,
      arguments: Option[Map[IR.Parameter, CheckExpression]] = None
  ): CheckExpression = {
    def resolve(input: IR.Expression) = resolveValue(input, arguments)

    input match {
      // These types can only be used at the "root" of a specification, not in an arbitrary
      // expression
      case _: IR.ArrayMember | _: IR.Imprecise | _: IR.PredicateInstance |
          _: IR.Accessibility =>
        throw new WeaverException("Invalid specification value")

      case n: IR.Var =>
        arguments match {
          case None => CheckExpression.Var(n.name)
          case Some(arguments) =>
            n match {
              case p: IR.Parameter =>
                arguments.getOrElse(
                  p,
                  throw new WeaverException(s"Unknown parameter '${p.name}'")
                )
              case v =>
                throw new WeaverException(s"Unknown variable '${v.name}'")
            }
        }

      case n: IR.FieldMember =>
        CheckExpression.Field(
          resolve(n.root),
          n.field.struct.name,
          n.field.name
        )
      case n: IR.DereferenceMember => CheckExpression.Deref(resolve(n.root))
      case n: IR.Result            => CheckExpression.Result
      case n: IR.IntLit            => CheckExpression.IntLit(n.value)
      case n: IR.CharLit           => CheckExpression.CharLit(n.value)
      case n: IR.BoolLit           => CheckExpression.BoolLit(n.value)
      case n: IR.StringLit         => CheckExpression.StrLit(n.value)
      case n: IR.NullLit           => CheckExpression.NullLit
      case n: IR.Conditional =>
        CheckExpression.Cond(
          resolve(n.condition),
          resolve(n.ifTrue),
          resolve(n.ifFalse)
        )
      case n: IR.Binary => {
        val l = resolve(n.left)
        val r = resolve(n.right)
        n.operator match {
          case IR.BinaryOp.Add      => CheckExpression.Add(l, r)
          case IR.BinaryOp.Subtract => CheckExpression.Sub(l, r)
          case IR.BinaryOp.Divide   => CheckExpression.Div(l, r)
          case IR.BinaryOp.Multiply => CheckExpression.Mul(l, r)
          case IR.BinaryOp.And      => CheckExpression.And(l, r)
          case IR.BinaryOp.Or       => CheckExpression.Or(l, r)
          case IR.BinaryOp.Equal    => CheckExpression.Eq(l, r)
          case IR.BinaryOp.NotEqual =>
            CheckExpression.Not(CheckExpression.Eq(l, r))
          case IR.BinaryOp.Less           => CheckExpression.Lt(l, r)
          case IR.BinaryOp.LessOrEqual    => CheckExpression.LtEq(l, r)
          case IR.BinaryOp.Greater        => CheckExpression.Gt(l, r)
          case IR.BinaryOp.GreaterOrEqual => CheckExpression.GtEq(l, r)
        }
      }
      case n: IR.Unary => {
        val o = resolve(n.operand)
        n.operator match {
          case IR.UnaryOp.Not    => CheckExpression.Not(o)
          case IR.UnaryOp.Negate => CheckExpression.Neg(o)
        }
      }
    }
  } */