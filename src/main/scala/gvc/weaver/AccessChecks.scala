package gvc.weaver
import gvc.transformer.IRGraph._
import viper.silicon.state.reconstructedPermissions.getPermissionsFor
import viper.silicon.state.CheckInfo
import viper.silver.ast.{FieldAccess, LocalVar, MethodCall}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class AccessCheckException(message: String) extends Exception(message)

object AccessChecks {

  private object Names {
    val InstanceCounter = "_instance_counter"
    val DynamicOwnedFields = "dyn_fields"
    val StaticOwnedFields = "static_fields"
    val TempStaticOwnedFields = "temp_static_fields"
    val TempDynamicOwnedFields = "temp_dyn_fields"
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
        new ArrayType(new ReferenceType(Structs.OwnedFields)),
        name = Names.TempDynamicOwnedFields
      )
    }
  }

  private object Methods {
    def InitOwnedFields: Method = {
      new Method(
        "initOwnedFields",
        Some(BoolType),
        None,
        None
      )
    }
    def AddFieldAccess: Method = {
      new Method(
        "addAccess",
        Some(BoolType),
        None,
        None
      )
    }
    def Assert: Method = {
      new Method(
        "assertAcc",
        Some(BoolType),
        None,
        None
      )
    }

    def AssertDisjoint: Method = {
      new Method(
        "assertDisjointAcc",
        Some(BoolType),
        None,
        None
      )
    }
    def AddStructAccess: Method = {
      new Method(
        "addStructAccess",
        Some(IntType),
        None,
        None
      )
    }
    def Join: Method = {
      new Method(
        "join",
        Some(BoolType),
        None,
        None
      )
    }
    def Disjoin: Method = {
      new Method(
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
      Vars.DynamicOwnedFields
    )
  }

  private def isImprecise(method: Method): Boolean = {
    optionImprecise(method.precondition) || optionImprecise(
      method.postcondition
    )
  }

  private def optionImprecise(expr: Option[Expression]): Boolean = {
    expr match {
      case Some(_: Imprecise) => true
      case _                  => false
    }
  }

  class ProgramAccessTracker(){
    var callGraph: Map[Method, MethodAccessTracker] = Map[Method, MethodAccessTracker]()
    var invocations: Map[Method, ArrayBuffer[Invoke]] = Map[Method, ArrayBuffer[Invoke]]()
    var runtimeChecksInserted: Boolean = false
    var entry: Option[Method] = None

    var visitedStructs: Set[Struct] = Set[Struct]()
    def register(method: Method, tracker: MethodAccessTracker): Unit = {
      callGraph += (method -> tracker)
      if(tracker.bodyContainsRuntimeCheck) runtimeChecksInserted = true
      if(method.name == "main") entry = Some(method)
      tracker.invocations.foreach(inv => {
        if(invocations.contains(inv.method)){
          invocations(inv.method) += inv
        }else{
          invocations += (inv.method -> ArrayBuffer(inv))
        }
      })
    }
  }

  class MethodAccessTracker(method: Method) {
    val callGraph = new CallGraph()
    var entry: Option[Method] = None
    val allocations: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    var invocations: mutable.ArrayBuffer[Invoke] = mutable.ArrayBuffer[Invoke]()
    var returns: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    var bodyContainsRuntimeCheck: Boolean = false
    def callsImprecise:Boolean = invocations.exists(inv => isImprecise(inv.method))

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
              if (check.overlaps) {
                new Invoke(
                  Methods.AssertDisjoint,
                  List(
                    Vars.StaticOwnedFields,
                    Commands.GetDynamicOwnedFields,
                    new FieldMember(variable, structType.fields.last),
                    getFieldIndex(structType, fieldName)
                  ),
                  None
                )
              } else {
                new Invoke(
                  Methods.Assert,
                  List(
                    Commands.GetDynamicOwnedFields,
                    new FieldMember(variable, structType.fields.last),
                    getFieldIndex(structType, fieldName)
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

  /* Tracks the callsites of each method, whether it calls an imprecise method, and where it returns.*/

  class Edge(
      var callsImprecise: Boolean,
      val callsites: mutable.Map[Op, InvokeInfo],
      val returns: mutable.ArrayBuffer[Op]
  )

  def needsStaticTracking(method: Method):Boolean = {
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

  class InvokeInfo(
      val callingMethod: Method,
      val vprNode: MethodCall
  )

  class CallGraph extends Iterable[(Method, Edge)] {
    override def iterator: Iterator[(Method, Edge)] = graph.iterator
    private var graph: Map[Method, Edge] = Map[Method, Edge]()

    def getEdge(method: Method): Option[Edge] = {
      if (graph.contains(method)) {
        Some(graph(method))
      } else {
        None
      }
    }

    def addEdge(
        calledMethod: Method,
        callPosition: Op,
        vprNode: MethodCall,
        callingMethod: Method
    ): Unit = {
      val entry = callPosition -> new InvokeInfo(
        callingMethod,
        vprNode
      )
      if (graph isDefinedAt calledMethod) {
        graph(calledMethod).callsites += entry
      } else {
        val edge = new Edge(
          callsImprecise = false,
          mutable.Map[Op, InvokeInfo](entry),
          mutable.ArrayBuffer[Op]()
        )
        graph += calledMethod -> edge
      }
      if (isImprecise(calledMethod)) {
        if (!(graph isDefinedAt callingMethod)) {
          graph += callingMethod -> new Edge(
            callsImprecise = true,
            mutable.Map[Op, InvokeInfo](),
            mutable.ArrayBuffer[Op]()
          )
        } else {
          graph(callingMethod).callsImprecise = true
        }
      }
    }
    def addReturn(returnPosition: Op, returningMethod: Method): Unit = {
      if (graph isDefinedAt returningMethod) {
        graph(returningMethod).returns += returnPosition
      } else {
        graph += returningMethod -> new Edge(
          callsImprecise = false,
          mutable.Map[Op, InvokeInfo](),
          mutable.ArrayBuffer[Op](returnPosition)
        )
      }
    }
  }

  def injectSupport(ir: Program, tracker: ProgramAccessTracker): Unit = {
    /*  it's only necessary to add tracking if a field access check was inserted,
     *  at which point the method where the check occurs is marked as 'visited' by the
     *  AccessTracker.
     */
    if (tracker.runtimeChecksInserted) {
      for ((caller: Method, edge: MethodAccessTracker) <- tracker.callGraph) {
        /* Modify the parameters of each method to accept OwnedFields objects as necessary */

        /* track each allocation, using _instance_counter or dynamic_fields as appropriate
       * to assign unique IDs to struct instances
       * */
        edge.allocations.foreach {
          case structAlloc: AllocStruct =>
            /* if a struct allocation occurs in an imprecise context, it's unique identifier is provided
             * by the dynamic_fields object, and permissions to each of its fields are recorded.
             */
            if (isImprecise(caller) || edge.callsImprecise) {
              injectIDField(structAlloc.struct, tracker)
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


        if (isImprecise(caller) && edge.callsImprecise)
          injectParameters(caller, tracker.invocations.get(caller), edge.returns)

        /* Pass the necessary OwnedFields objects when each method is called */
        for (invocation <- edge.invocations) {
          var afterwards:Op = invocation
          val callee = invocation.callee
          while (
            afterwards.getNext.isDefined
            && afterwards.getNext.get.isInstanceOf[Invoke]
            && (afterwards.getNext.get
              .asInstanceOf[Invoke]
              .method
              .name == "assertAcc" || afterwards.getNext.get
              .asInstanceOf[Invoke]
              .method
              .name == "assertDisjointAcc")
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
                new ArrayType(new ReferenceType(Structs.OwnedFields)),
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
              invocation.insertBefore(
                populateStatic(Vars.StaticOwnedFields, callee.precondition)
              )

              invocation.insertBefore(
                Commands.Disjoin(
                  Commands.GetDynamicOwnedFields,
                  Vars.StaticOwnedFields
                )
              )

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
              afterwards.insertAfter(
                populateStatic(
                  Commands.GetDynamicOwnedFields,
                  callee.postcondition
                )
              )
            } else {
              if (needsStatic) {
                afterwards.insertAfter(Commands.StoreStatic)
              }
              invocation.insertBefore(Commands.InitStatic)
              invocation.insertBefore(
                populateStatic(Vars.StaticOwnedFields, callee.precondition)
              )

              invocation.insertBefore(Commands.StoreDynamic)
              invocation.insertBefore(Commands.InitDynamic)

              if (needsStatic) {
                afterwards.insertAfter(Commands.StoreStatic)

                afterwards.insertAfter(
                  Commands.Disjoin(
                    Vars.DynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
                afterwards.insertAfter(Commands.LoadStatic)
              }
              afterwards.insertAfter(
                Commands.Join(
                  Vars.DynamicOwnedFields,
                  Vars.TempDynamicOwnedFields
                )
              )
              afterwards.insertAfter(
                populateStatic(
                  Vars.StaticOwnedFields,
                  callee.precondition
                )
              )

              if (optionImprecise(callee.postcondition)) {
                afterwards.insertAfter(
                  Commands.Join(
                    Vars.DynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
                afterwards.insertAfter(
                  Commands.Join(
                    Vars.DynamicOwnedFields,
                    Vars.StaticOwnedFields
                  )
                )
              }
            }
          } else {
            //TODO: optimize so that _instance_counter is only passed to methods that eventually allocate memory
            invocation.arguments =
              invocation.arguments ++ List(Vars.InstanceCounter)
          }
        }
      }

      /*  initialize _instance_counter at the beginning of main. if a runtime check is required in main,
       *  instructions to create the necessary OwnedFields objects will have already been inserted, so it is safe
       *  to initialize _instance_counter as the final step here.
       */
      tracker.entry match {
        case Some(mainMethod) =>
          mainMethod.addVar(new PointerType(IntType), Names.InstanceCounter)
          mainMethod.body.head.insertBefore(Commands.InitCounter)
        case None => throw new AccessCheckException("The current ProgramAccessTracker instance hasn't detected a main method for the given program.")
      }
    }
  }

  case class AccessPermission(
      root: Expression,
      struct: Struct,
      fieldName: String
  )

  def getAccessPermissionsAt(
      call: MethodCall,
      callingMethod: Method
  ): mutable.Set[AccessPermission] = {
    val accessSet = mutable.Set[AccessPermission]()
    getPermissionsFor(call).foreach {
      case fa: FieldAccess =>
        fa.rcv match {
          case LocalVar(name, _) =>
            val fieldName =
              fa.field.name.substring(fa.field.name.lastIndexOf('$') + 1)
            callingMethod.getVar(name) match {
              case Some(variable) =>
                val structType =
                  variable.valueType.asInstanceOf[ReferenceType].struct
                accessSet += AccessPermission(variable, structType, fieldName)
              case None => throw new AccessCheckException(s"The variable $name, which is required for access tracking, hasn't been declared in the current method.")
            }
          case _ => throw new AccessCheckException("Access tracking is only enabled for local variables.")
        }
      case _ =>
        throw new AccessCheckException(
          "Only field permissions for structs that are LocalVars have been implemented."
        )
    }
    accessSet
  }
  def populateOwnedFields(
      call: MethodCall,
      caller: Method,
      spec: Option[Expression]
  ): Seq[Op] = {

    val static: mutable.Set[AccessPermission] = getStaticComponent(spec)
    val available_permissions: mutable.Set[AccessPermission] =
      getAccessPermissionsAt(call, caller)
    val dynamic = available_permissions.diff(static)
    val ops: mutable.ArrayBuffer[Op] = mutable.ArrayBuffer[Op]()
    dynamic.foreach(perm => {
      ops += addFieldAccess(Commands.GetDynamicOwnedFields, perm)
    })
    static.foreach(perm => {
      ops += addFieldAccess(Vars.StaticOwnedFields, perm)
    })
    ops
  }

  def populateStatic(
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

  def getStaticComponent(
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

  def toAccessPermission(acc: Accessibility): AccessPermission = {
    acc.member match {
      case member: FieldMember =>
        AccessPermission(member.root, member.field.struct, member.field.name)
      case _ =>
        throw new AccessCheckException("Unimplemented field access type.")
    }
  }

  def injectParameters(
      method: Method,
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
          ret.insertBefore(
            new AssignIndex(
              Vars.DynamicOwnedFields,
              new Int(0),
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

  def getFieldIndex(structType: Struct, fieldName: String): Int = {
    val index =
      structType.fields.indexWhere(field => field.name.equals(fieldName))
    new Int(index)
  }

  def injectIDField(structType: Struct, tracker: ProgramAccessTracker): Unit = {
    if (!tracker.visitedStructs.contains(structType)) {
      structType.addField(Names.ID, IntType)
      tracker.visitedStructs += structType
    }
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

  def addDynamicStructAccess(
      exprToDeref: Expression,
      structType: Struct
  ): Op = {
    addStructAccess(
      Commands.GetDynamicOwnedFields,
      exprToDeref,
      structType
    )
  }

  def addStaticStructAccess(
      exprToDeref: Expression,
      structType: Struct
  ): Op = {
    addStructAccess(Vars.StaticOwnedFields, exprToDeref, structType)
  }
}
