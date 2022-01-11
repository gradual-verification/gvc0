package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silicon.state.CheckInfo
import viper.silver.ast.{FieldAccess, LocalVar}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class AccessCheckException(message: java.lang.String) extends Exception(message)

object AccessChecks {
  private object Names {
    val InstanceCounter = "_instance_counter"
    val DynamicOwnedFields = "dyn_fields"
    val StaticOwnedFields = "static_fields"
    val TempStaticOwnedFields = "temp_static_fields"
    val TempDynamicOwnedFields = "temp_dyn_fields"
    val AssertAcc = "assertAcc"
    val AssertDisjointAcc = "assertDisjointAcc"
    val ID = "_id"
  }

  private object Structs {
    def OwnedFields = new Struct("OwnedFields")
  }

  private object Vars {
    def InstanceCounter: Var = {
      new Var(new PointerType(IntType), Names.InstanceCounter)
    }

    def StaticOwnedFields: Var = {
      new Var(
        new ReferenceType(Structs.OwnedFields),
        name = Names.StaticOwnedFields
      )
    }

    def DynamicOwnedFields: Var = {
      new Var(
        new ArrayType(new ReferenceType(Structs.OwnedFields)),
        name = Names.DynamicOwnedFields
      )
    }

    def TempStaticOwnedFields: Var = {
      new Var(
        new ReferenceType(Structs.OwnedFields),
        name = Names.TempStaticOwnedFields
      )
    }

    def TempDynamicOwnedFields: Var = {
      new Var(
        new ReferenceType(Structs.OwnedFields),
        name = Names.TempDynamicOwnedFields
      )
    }
  }

  private object Methods {
    def InitOwnedFields: MethodImplementation = {
      new MethodImplementation(
        "initOwnedFields",
        Some(BoolType),
        None,
        None
      )
    }

    def AddFieldAccess: MethodImplementation = {
      new MethodImplementation(
        "addAccess",
        Some(BoolType),
        None,
        None
      )
    }

    def LoseFieldAccess: MethodImplementation = {
      new MethodImplementation(
        "loseAccess",
        Some(BoolType),
        None,
        None
      )
    }

    def Assert: MethodImplementation = {
      new MethodImplementation(
        Names.AssertAcc,
        Some(BoolType),
        None,
        None
      )
    }

    def AssertDisjoint: MethodImplementation = {
      new MethodImplementation(
        Names.AssertDisjointAcc,
        Some(BoolType),
        None,
        None
      )
    }

    def AddStructAccess: MethodImplementation = {
      new MethodImplementation(
        "addStructAccess",
        Some(IntType),
        None,
        None
      )
    }

    def Join: MethodImplementation = {
      new MethodImplementation(
        "join",
        Some(BoolType),
        None,
        None
      )
    }

    def Disjoin: MethodImplementation = {
      new MethodImplementation(
        "disjoin",
        Some(BoolType),
        None,
        None
      )
    }
  }

  private object Commands {
    def InitCounter: Seq[Op] = {
      Seq(
        new AllocValue(IntType, Vars.InstanceCounter),
        new AssignMember(
          new DereferenceMember(Vars.InstanceCounter, IntType),
          new Int(0)
        )
      )
    }

    def InitStatic: Seq[Op] = {
      Seq(
        new AllocStruct(Structs.OwnedFields, Vars.StaticOwnedFields),
        new Invoke(
          Methods.InitOwnedFields,
          List(Vars.StaticOwnedFields, Vars.InstanceCounter),
          None
        )
      )
    }

    def InitDynamic: Seq[Op] = {
      Seq(
        new AllocArray(
          new ReferenceType(Structs.OwnedFields),
          new Int(1),
          Vars.DynamicOwnedFields
        ),
        new AllocStruct(
          Structs.OwnedFields,
          new ArrayMember(
            Vars.DynamicOwnedFields,
            Vars.DynamicOwnedFields.valueType,
            new Int(0)
          )
        ),
        new Invoke(
          Methods.InitOwnedFields,
          List(
            Commands.GetDynamicOwnedFields,
            Vars.InstanceCounter
          ),
          None
        )
      )
    }

    def GetDynamicOwnedFields: ArrayMember = {
      new ArrayMember(
        Vars.DynamicOwnedFields,
        new ReferenceType(Structs.OwnedFields),
        new Int(0)
      )
    }

    def Join(target: Expression, src: Expression): Invoke = {
      new Invoke(
        Methods.Join,
        List(
          target,
          src
        ),
        None
      )
    }

    def Disjoin(target: Expression, src: Expression): Invoke = new Invoke(
      Methods.Disjoin,
      List(
        target,
        src
      ),
      None
    )

    def StoreStatic: Assign = new Assign(
      Vars.TempStaticOwnedFields,
      Vars.StaticOwnedFields
    )

    def LoadStatic: Assign = new Assign(
      Vars.StaticOwnedFields,
      Vars.TempStaticOwnedFields
    )

    def StoreDynamic: Assign = new Assign(
      Vars.TempDynamicOwnedFields,
      Commands.GetDynamicOwnedFields
    )
  }

  private def isImprecise(method: MethodImplementation): Boolean = {
    optionImprecise(method.precondition) || optionImprecise(
      method.postcondition
    )
  }

  private def optionImprecise(expr: Option[Expression]): Boolean = {
    expr match {
      case Some(_: Imprecise) => true
      case _ => false
    }
  }

  class ProgramAccessTracker(ir: Program) {
    var callGraph: Map[MethodImplementation, MethodAccessTracker] = Map[MethodImplementation, MethodAccessTracker]()
    var invocations: Map[MethodImplementation, ArrayBuffer[Invoke]] = Map[MethodImplementation, ArrayBuffer[Invoke]]()
    var runtimeChecksInserted: Boolean = false
    var entry: Option[MethodImplementation] = None
    var allocatesMemory: Set[MethodImplementation] = Set[MethodImplementation]()
    val visitedStructs: mutable.Set[Struct] = mutable.Set[Struct]()

    def mergeTracker(method: MethodImplementation, tracker: MethodAccessTracker): Unit = {
      callGraph += (method -> tracker)
      if (tracker.bodyContainsRuntimeCheck) runtimeChecksInserted = true
      if (method.name == "main") entry = Some(method)
      tracker.invocations.foreach(inv => {
        inv.callee match {
          case callee: MethodImplementation => {
            if (invocations.contains(callee)) {
              invocations(callee) += inv
            } else {
              invocations += (callee -> ArrayBuffer(inv))
            }
          }
          case _ => ()
        }
        
      })
      if (tracker.allocations.nonEmpty) allocatesMemory += method
    }

    def spawnTracker(method: MethodImplementation): MethodAccessTracker = {
      new MethodAccessTracker(method, visitedStructs)
    }

    def injectSupport(): Unit = {
      /*  it's only necessary to add tracking if a field access check was inserted,
       *  at which point the method where the check occurs is marked as 'visited' by the
       *  AccessTracker.
       */

      for ((caller: MethodImplementation, edge: MethodAccessTracker) <- callGraph) {
        /* Modify the parameters of each method to accept OwnedFields objects as necessary */

        /* track each allocation, using _instance_counter or dynamic_fields as appropriate
         * to assign unique IDs to struct instances
         * */

        edge.injectAllocationTracking()
        injectParameters(caller, invocations.get(caller), edge.returns)

        edge.returns.foreach(ret => {
          ret.insertBefore(populateStatic(Vars.StaticOwnedFields, caller.postcondition))
        })

        /* Pass the necessary OwnedFields objects when each method is called */
        for (invocation <- edge.invocations) {
          var afterwards: Op = invocation
          val callee = invocation.callee.asInstanceOf[MethodImplementation]
          while (
            afterwards.getNext.isDefined
              && afterwards.getNext.get.isInstanceOf[Invoke]
              && (afterwards.getNext.get
              .asInstanceOf[Invoke]
              .callee
              .name == Names.AssertAcc || afterwards.getNext.get
              .asInstanceOf[Invoke]
              .callee
              .name == Names.AssertDisjointAcc)
          ) afterwards = afterwards.getNext.get

          val needsStatic = needsStaticTracking(callee)

          if (isImprecise(callee)) {

            if (!isImprecise(caller)) {
              caller.addVar(
                new ArrayType(new ReferenceType(Structs.OwnedFields)),
                Names.DynamicOwnedFields
              )
              caller.body.head
                .insertBefore(Commands.InitDynamic)

              if (needsStatic) {
                caller.addVar(
                  new ReferenceType(Structs.OwnedFields),
                  Names.TempStaticOwnedFields
                )
              }
              caller.addVar(
                new ReferenceType(Structs.OwnedFields),
                Names.StaticOwnedFields
              )
              caller.addVar(
                new ReferenceType(Structs.OwnedFields),
                Names.TempDynamicOwnedFields
              )
            }

            if (optionImprecise(callee.precondition)) {

              if (needsStatic) {
                invocation.insertBefore(Commands.StoreStatic)
                invocation.insertBefore(
                  Commands.Join(
                    Commands.GetDynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
              }

              invocation.insertBefore(Commands.InitStatic)

              callee.body.head.insertBefore(Commands.Disjoin(
                Commands.GetDynamicOwnedFields,
                Vars.StaticOwnedFields
              ))

              callee.body.head.insertBefore(populateStatic(Vars.StaticOwnedFields, callee.precondition))

              if (needsStatic) {
                afterwards.insertAfter(
                  Commands.Disjoin(
                    Commands.GetDynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
                afterwards.insertAfter(Commands.LoadStatic)
              }

              afterwards.insertAfter(
                Commands.Join(
                  Commands.GetDynamicOwnedFields,
                  Vars.StaticOwnedFields
                )
              )
            } else {
              if (needsStatic) {
                afterwards.insertAfter(Commands.StoreStatic)
              }
              invocation.insertBefore(Commands.InitStatic)

              invocation.insertBefore(Commands.StoreDynamic)
              invocation.insertBefore(Commands.InitDynamic)

              if (needsStatic) {
                afterwards.insertAfter(Commands.StoreStatic)

                afterwards.insertAfter(
                  Commands.Disjoin(
                    Commands.GetDynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
                afterwards.insertAfter(Commands.LoadStatic)
              }
              afterwards.insertAfter(
                Commands.Join(
                  Commands.GetDynamicOwnedFields,
                  Vars.TempDynamicOwnedFields
                )
              )

              if (optionImprecise(callee.postcondition)) {
                afterwards.insertAfter(
                  Commands.Join(
                    Commands.GetDynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
              }
            }
          } else {
            //TODO: optimize so that _instance_counter is only passed to methods that eventually allocate memory
            invocation.arguments =
              invocation.arguments ++ List(Vars.InstanceCounter)
            if (edge.callsImprecise) {
              val byPrecondition = getStaticComponent(callee.precondition)
              val byPostcondition = getStaticComponent(callee.postcondition)

              val toRemove = byPrecondition.diff(byPostcondition)
              val toAdd = byPostcondition.diff(byPrecondition)

              toRemove.foreach(perm => {
                invocation.insertAfter(loseFieldAccess(perm))
              })
              toAdd.foreach(perm => {
                invocation.insertAfter(loseFieldAccess(perm))
              })
            }
          }
        }
      }

      /*  initialize _instance_counter at the beginning of main. if a runtime check is required in main,
         *  instructions to create the necessary OwnedFields objects will have already been inserted, so it is safe
         *  to initialize _instance_counter as the final step here.
         */
      entry match {
        case Some(mainMethod) =>
          mainMethod.addVar(new PointerType(IntType), Names.InstanceCounter)
          if (mainMethod.body.nonEmpty) {
            mainMethod.body.head.insertBefore(Commands.InitCounter)
          }
        case None => throw new AccessCheckException("The current ProgramAccessTracker instance hasn't detected a main method for the given program.")
      }
      // TODO: ir.addDependency("runtime", isLibrary=true)
    }
  }

  class MethodAccessTracker(method: MethodImplementation, visitedStructs: mutable.Set[Struct]) {
    var entry: Option[MethodImplementation] = None
    val allocations: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    var invocations: mutable.ArrayBuffer[Invoke] = mutable.ArrayBuffer[Invoke]()
    var returns: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    var bodyContainsRuntimeCheck: Boolean = false

    def callsImprecise: Boolean = invocations.exists(inv => isImprecise(inv.callee.asInstanceOf[MethodImplementation]))

    def injectAllocationTracking():Unit = {
      allocations.foreach {
        case structAlloc: AllocStruct =>
          /* if a struct allocation occurs in an imprecise context, it's unique identifier is provided
           * by the dynamic_fields object, and permissions to each of its fields are recorded.
           */
          if (isImprecise(method) || callsImprecise) {
            structAlloc.insertAfter(
              addDynamicStructAccess(
                structAlloc.target,
                structAlloc.struct
              )
            )
          } else {

            /* If it occurs in a fully-verified context, then the _instance_counter parameter is used to assign the ID
             * and is incremented. If this code is reached, we can assume that a field access runtime check must
             * occur elsewhere, so tracking allocations in fully-verified contexts is necessary. The following operations
             * occur in reverse order:
             */

            /* increment *(_instance_counter) */
            val deref_inst_counter =
              new DereferenceMember(Vars.InstanceCounter, IntType)

            structAlloc.insertAfter(
              new AssignMember(
                deref_inst_counter,
                new Binary(
                  BinaryOp.Add,
                  deref_inst_counter,
                  new Int(1)
                )
              )
            )
            /* assign the new instance's _id field to the current value of *(_instance_counter) */
            structAlloc.insertAfter(
              new AssignMember(
                new FieldMember(
                  structAlloc.target,
                  new StructField(structAlloc.struct, Names.ID, IntType)
                ),
                new DereferenceMember(Vars.InstanceCounter, IntType)
              )
            )
          }
        case _ => throw new AccessCheckException("Access tracking has only implemented for Struct allocations.")
      }
    }

    def assertFieldAccess(
                           check: CheckInfo,
                           loc: FieldAccess,
                         ): Op = {
      bodyContainsRuntimeCheck = true
      val fieldName =
        loc.field.name.substring(loc.field.name.lastIndexOf('$') + 1)
      loc.rcv match {
        case LocalVar(name, _) =>
          method.getVar(name) match {
            case Some(variable) =>
              val structType =
                variable.valueType.asInstanceOf[ReferenceType].struct
              if (!visitedStructs.contains(structType)) {
                structType.addField(Names.ID, IntType)
                visitedStructs += structType
              }
              val structAndField = loc.field.name
              val errorMessage: String = new String(s"Field access check failed for $structAndField.")
              if (check.overlaps) {
                new Invoke(
                  Methods.AssertDisjoint,
                  List(
                    Vars.StaticOwnedFields,
                    Commands.GetDynamicOwnedFields,
                    new FieldMember(variable, structType.fields.last),
                    getFieldIndex(structType, fieldName),
                    errorMessage
                  ),
                  None
                )
              } else {
                new Invoke(
                  Methods.Assert,
                  List(
                    Commands.GetDynamicOwnedFields,
                    new FieldMember(variable, structType.fields.last),
                    getFieldIndex(structType, fieldName),
                    errorMessage
                  ),
                  None
                )
              }
            case None =>
              throw new AccessCheckException(
                "No local variable exists for the given field permission."
              )
          }
        case _ =>
          throw new AccessCheckException(
            "Only field permissions for structs that are LocalVars have been implemented."
          )
      }
    }
  }

  private def needsStaticTracking(method: MethodImplementation): Boolean = {
    val preStatic = method.precondition.isDefined && method.precondition.get
      .isInstanceOf[Imprecise] && method.precondition.get
      .asInstanceOf[Imprecise]
      .precise
      .isDefined
    val postStatic = method.postcondition.isDefined && method.postcondition.get
      .isInstanceOf[Imprecise] && method.postcondition.get
      .asInstanceOf[Imprecise]
      .precise
      .isDefined
    postStatic || preStatic
  }

  private case class AccessPermission(
                                       root: Expression,
                                       struct: Struct,
                                       fieldName: java.lang.String
                                     )

  private def populateStatic(
                              target: Expression,
                              spec: Option[Expression]
                            ): Seq[Op] = {
    val accessSet = getStaticComponent(spec)
    val ops: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    accessSet.foreach(perm => {
      ops += addFieldAccess(target, perm)
    })
    ops
  }

  private def getStaticComponent(
                                  expression: Option[Expression]
                                ): mutable.Set[AccessPermission] = {
    val access = mutable.Set[AccessPermission]()
    expression match {
      case Some(expr) =>
        expr match {
          case imp: Imprecise =>
            access ++ getStaticComponent(imp.precise)
          case bin: Binary =>
            bin.right match {
              case acc: Accessibility =>
                access += toAccessPermission(acc)
                access ++ getStaticComponent(Some(bin.left))
              case _ => throw new AccessCheckException("Unknown conjunct type.")
            }
          case acc: Accessibility =>
            access += toAccessPermission(acc)
            access
          case _ => throw new AccessCheckException("Unknown conjunct type.")
        }
      case None => access
    }
  }

  private def toAccessPermission(acc: Accessibility): AccessPermission = {
    acc.member match {
      case member: FieldMember =>
        AccessPermission(member.root, member.field.struct, member.field.name)
      case _ =>
        throw new AccessCheckException("Unimplemented field access type.")
    }
  }

  private def injectParameters(
                                method: MethodImplementation,
                                callsites: Option[Iterable[Invoke]],
                                returns: Iterable[Op]
                              ): Unit = {
    /* imprecise methods are passed two disjoint OwnedFields structs: one containing the fields that are statically
     * accessible at the method's callsite, and the other containing all other field access permissions that have been
     * recorded throughout runtime at every call to alloc.
     */
    if (isImprecise(method) && method.name != "main") {
      method.addParameter(
        Vars.DynamicOwnedFields.valueType,
        Names.DynamicOwnedFields
      )
      method.addParameter(
        Vars.StaticOwnedFields.valueType,
        Names.StaticOwnedFields
      )

      callsites match {
        case Some(sites) =>
          sites.foreach(site => {
            site.arguments = site.arguments ++ List(
              Vars.DynamicOwnedFields,
              Vars.StaticOwnedFields
            )
          })
        case None =>
      }

      /* when an imprecise method returns, if its postcondition is precise, then only the statically verified fields of the
       * postcondition will be returned to the caller.
       */
      if (
        method.postcondition.isDefined && !optionImprecise(method.postcondition)
      ) {
        returns.foreach(ret => {
          ret.insertBefore(new AssignMember(
            Commands.GetDynamicOwnedFields,
            Vars.StaticOwnedFields
          )
          )
        })
      }
    } else {
      /* fully verified methods are passed the _instance_counter to assign unique IDs to each struct allocation */
      if (method.name != "main")
        method.addParameter(new PointerType(IntType), Names.InstanceCounter)

    }
  }

  private def getFieldIndex(structType: Struct, fieldName: java.lang.String): Int = {
    val index =
      structType.fields.indexWhere(field => field.name.equals(fieldName))
    new Int(index)
  }

  private def addFieldAccess(
                              fields: Expression,
                              perm: AccessPermission
                            ): Invoke = {
    new Invoke(
      Methods.AddFieldAccess,
      List(
        fields,
        new FieldMember(perm.root, perm.struct.fields.last),
        new Int(perm.struct.fields.length - 1),
        getFieldIndex(perm.struct, perm.fieldName)
      ),
      None
    )
  }

  private def loseFieldAccess(perm: AccessChecks.AccessPermission): Invoke = {
    new Invoke(
      Methods.LoseFieldAccess,
      List(
        Vars.StaticOwnedFields,
        Commands.GetDynamicOwnedFields,
        new FieldMember(perm.root, perm.struct.fields.last),
        getFieldIndex(perm.struct, perm.fieldName)
      ),
      None
    )
  }

  private def addStructAccess(
    fields: Expression,
    exprToDeref: Expression,
    structType: Struct
  ): Op = {
    new Invoke(
      Methods.AddStructAccess,
      List(fields, new Int(structType.fields.length - 1)),
      Some(
        new FieldMember(
          exprToDeref,
          new StructField(structType, Names.ID, IntType)
        )
      )
    )
  }

  private def addDynamicStructAccess(
      exprToDeref: Expression,
      structType: Struct
    ): Op = {
    addStructAccess(
      Commands.GetDynamicOwnedFields,
      exprToDeref,
      structType
    )

  }
}