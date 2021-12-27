package gvc.weaver
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph._
import viper.silicon.state.CheckInfo
import viper.silver.ast.{FieldAccess, LocalVar, Exp}

import scala.collection.mutable

object AccessChecks{

  private object Names {
    val InstanceCounter = "_instance_counter"
    val DynamicOwnedFields = "dyn_fields"
    val StaticOwnedFields = "static_fields"
    val ID = "_id"
  }
  private object Structs {
    def OwnedFields = new Struct("OwnedFields")
  }
  private object Vars {
    def InstanceCounter = new Var(new PointerType(IntType), Names.InstanceCounter)
    def StaticOwnedFields = new Var(new ReferenceType(Structs.OwnedFields), "static_fields")
    def DynamicOwnedFields = new Var(new ReferenceArrayType(Structs.OwnedFields), name=Names.DynamicOwnedFields)
  }
  private object Methods{
    def InitOwnedFields = new Method(
      "initOwnedFields",
      Some(BoolType),
      None,
      None
    )
    def AddFieldAccess = new Method(
      "addAccess",
      Some(BoolType),
      None,
      None
    )
    def AssertAcc = new Method(
      "assertAcc",
      Some(BoolType),
      None,
      None,
    )
    def Assert = new Method(
      "assertAccess",
      Some(BoolType),
      None,
      None,
    )
    def AssertDisjoint = new Method(
      "assertDisjointAccess",
      Some(BoolType),
      None,
      None,
    )

    def AddStructAccess = new Method(
      "addStructAccess",
      Some(IntType),
      None,
      None
    )
    def Join = new Method(
      "disjoin",
      Some(BoolType),
      None,
      None,
    )
    def Disjoin = new Method(
      "disjoin",
      Some(BoolType),
      None,
      None,
    )
  }
  private object Commands {
    def InitCounter = Seq(
      new AllocValue(IntType, Vars.InstanceCounter),
      new AssignMember(new DereferenceMember(Vars.InstanceCounter, IntType), new Int(0))
    )
    def InitStatic = Seq(
      new AllocStruct(Structs.OwnedFields, Vars.StaticOwnedFields),
      new Invoke(Methods.InitOwnedFields, List(Vars.StaticOwnedFields, Vars.InstanceCounter), None)
    )
    def InitDynamic = Seq(
      new AllocArray(new ReferenceType(Structs.OwnedFields), new Int(1), Vars.DynamicOwnedFields),
      new AllocStruct(Structs.OwnedFields, new ArrayMember(Vars.DynamicOwnedFields, Vars.DynamicOwnedFields.valueType, new Int(0))),
      new Invoke(Methods.InitOwnedFields, List(Commands.GetDynamicOwnedFields, Vars.InstanceCounter), None),
    )
    def Join = new Invoke(Methods.Join, List(Commands.GetDynamicOwnedFields, Vars.StaticOwnedFields), None)
    def Disjoin = new Invoke(Methods.Disjoin, List(Commands.GetDynamicOwnedFields, Vars.StaticOwnedFields), None)
    def GetDynamicOwnedFields = new ArrayMember(Vars.DynamicOwnedFields, new ReferenceType(Structs.OwnedFields), new Int(0))

  }

  private def isImprecise(method: Method):Boolean = {
    optionImprecise(method.precondition) || optionImprecise(method.postcondition)
  }

  private def optionImprecise(expr: Option[Expression]):Boolean = {
    expr match{
      case Some(_:Imprecise) => true
      case _ => false
    }
  }
  class Edge(var callsImprecise: Boolean, var callsites: mutable.ArrayBuffer[Op], var returns: mutable.ArrayBuffer[Op])


  class AccessTracker(){
    val callGraph = new CallGraph()
    var entry: Option[Method] = None
    private val visited: mutable.Set[String] = mutable.Set[String]()
    private val visitedStructs: mutable.Set[String] = mutable.Set[String]()
    val allocations: mutable.Set[(Method, Op)] = mutable.Set[(Method, Op)]()

    def requiresTracking(): Boolean = visited.nonEmpty

    def visitedStruct(structName: String): Boolean = {
      visitedStructs.contains(structName)
    }

    def visitStruct(structName: String): Unit = {
      visitedStructs += structName
    }

    def visitedMethod(method: Method): Boolean = {
      visited.contains(method.name)
    }

    def visitMethod(method: Method): Unit = {
      visited += method.name
    }

  }

  class CallGraph extends Iterable[(Method, Edge)]{
    override def iterator = graph.iterator;
    private var graph: Map[Method, Edge] = Map[Method, Edge]()

    def addEdge(calledMethod: Method, callPosition: Op, callingMethod: Method): Unit = {
      if (graph isDefinedAt calledMethod) {
        graph(calledMethod).callsites += callPosition
      } else {
        val edge = new Edge(callsImprecise = false, mutable.ArrayBuffer[Op](callPosition), mutable.ArrayBuffer[Op]())
        graph += calledMethod -> edge
      }
      if (isImprecise(calledMethod)) {
        if (!(graph isDefinedAt callingMethod)) {
          graph += callingMethod -> new Edge(callsImprecise = true, mutable.ArrayBuffer[Op](), mutable.ArrayBuffer[Op]())
        } else {
          graph(callingMethod).callsImprecise = true
        }
      }
    }
    def addReturn(returnPosition: Op, returningMethod: Method): Unit ={
      if(graph isDefinedAt returningMethod){
        graph(returningMethod).returns += returnPosition
      }else{
        graph += returningMethod -> new Edge(callsImprecise = false, mutable.ArrayBuffer[Op](), mutable.ArrayBuffer[Op](returnPosition))
      }
    }
  }

  def injectSupport(ir: Program, tracker: AccessTracker): Unit = {
    if (tracker.requiresTracking) {
      for ((method: Method, edge: Edge) <- tracker.callGraph) {
        injectParameters(method, edge, tracker)
        edge.callsites.foreach((position: Op) => {
          if(optionImprecise(method.precondition)) {
            position.insertBefore(Commands.Join)
          }
          if (optionImprecise(method.postcondition)) {
            position.insertAfter(Commands.Disjoin)
          }
        })
      }
      tracker.allocations.foreach(alloc => {
        val method = alloc._1
        val alloc_op = alloc._2
        alloc_op match {
          case structAlloc: AllocStruct =>
            if(isImprecise(method)){
              injectIDField(structAlloc.struct, tracker)
              structAlloc.insertAfter(addDynamicStructAccess(structAlloc.target, structAlloc.struct, tracker))
            }else{
              //assign and increment _id_counter
            }
        }
      })
      tracker.entry match {
        case Some(mainMethod) =>
          mainMethod.addExistingVar(Vars.InstanceCounter)
          mainMethod.body.head.insertBefore(Commands.InitCounter)
      }

      for (method <- tracker.visited) {

      }
    }
  }

  def injectParameters(method: Method, edge:Edge, tracker: AccessTracker): Unit = {
    if (isImprecise(method)) {
      method.addParameter(Vars.DynamicOwnedFields.valueType , Names.DynamicOwnedFields)
      method.addParameter(Vars.StaticOwnedFields.valueType, Names.StaticOwnedFields)
      edge.callsites.foreach(site => {
        collectStaticPermissions(site, method, tracker)
      })
      if (method.postcondition.isDefined && !optionImprecise(method.postcondition)) {
        for (ret <- edge.returns) {
          ret.insertBefore(new AssignIndex(Vars.DynamicOwnedFields, new Int(0), Vars.StaticOwnedFields))
        }
      }
    } else {
      method.addParameter(new PointerType(IntType), Names.InstanceCounter)
      if (edge.callsImprecise) {
        method.addExistingVar(Vars.DynamicOwnedFields)
        method.body.head.insertBefore(Commands.InitDynamic)
      }
    }
  }

  def collectStaticPermissions(site: Op, method: Method, tracker: AccessTracker): Unit = {
    val permissions = getPermissionsFor
  }

  def generateStaticTracker(method: Method, tracker: AccessTracker): Unit = {
    val staticFieldInitialization = mutable.ArrayBuffer[Op]()
    val accessibilityPredicates = collectStaticPermissions(method.precondition)
    accessibilityPredicates.foreach(acc => {
      acc.member match {
        case member: FieldMember =>
           staticFieldInitialization += addFieldAccess(
            Vars.StaticOwnedFields,
            member.root,
            member.field.struct,
            member.field.name, tracker
          )
        case _: DereferenceMember => throw new WeaverException("Field access check implementation doesn't exist for DereferenceMember.")
      }
    })
    method.addExistingVar(Vars.StaticOwnedFields)
    method.body.head.insertBefore(Commands.InitStatic)
    method.body.head.insertBefore(staticFieldInitialization)
  }


  def collectStaticPermissions(expression: Option[Expression]): mutable.ArrayBuffer[Accessibility] = {
    val access = mutable.ArrayBuffer[Accessibility]()
    expression match {
      case Some(expr) =>
        expr match {
          case imp: IRGraph.Imprecise =>
            access ++ collectStaticPermissions(imp.precise)
          case bin: IRGraph.Binary =>
            bin.right match {
              case acc: Accessibility =>
                access += acc
                access ++ collectStaticPermissions(Some(bin.left))
              case _ => throw new WeaverException("Unknown conjunct type.")
            }
          case acc: IRGraph.Accessibility =>
            access += acc
            access
          case _ => throw new WeaverException("Unknown conjunct type.")
        }
      case None => access

    }
  }

  def getFieldIndex(structType: Struct, fieldName: String): Int = {
    val index = structType.fields.indexWhere(field => field.name.equals(fieldName))
    new Int(index)
  }

  def injectIDField(structType: Struct, tracker: AccessTracker): Unit = {
    if (!tracker.visitedStruct(structType.name)) {
      structType.addField(Names.ID, IntType)
      tracker.visitStruct(structType.name)
    }
  }

  def generateAccessCheck(info: CheckInfo, loc: FieldAccess, toDeref: Expression, structType: Struct, fieldName: String): Seq[Op] = {
    if (info.overlaps && !isStaticallyVerifiedField(loc)) {
      Seq(new Invoke(
        Methods.AssertDisjoint,
        List(Vars.StaticOwnedFields,
          Commands.GetDynamicOwnedFields,
          new FieldMember(toDeref, structType.fields.last),
          getFieldIndex(structType, fieldName)),
        None
      ))
    } else {
      Seq(new Invoke(
        Methods.Assert,
        List(Commands.GetDynamicOwnedFields,
          new FieldMember(toDeref, structType.fields.last),
          getFieldIndex(structType, fieldName)),
        None
      ))
    }
  }

  def isStaticallyVerifiedField(loc: FieldAccess): Boolean = {
    true
  }

  def assertFieldAccess(check: CheckInfo, loc: FieldAccess, method: Method, tracker: AccessTracker): Seq[Op] = {
    val fieldName = loc.field.name.substring(loc.field.name.lastIndexOf('$') + 1)
    loc.rcv match {
      case LocalVar(name, _) =>
        method.getVar(name) match {
          case Some(variable) =>
            val structType = variable.valueType.asInstanceOf[ReferenceType].struct
            injectIDField(structType, tracker)
            generateAccessCheck(check, loc, variable, structType, fieldName)
          case None => ???
        }
      case _ => ???
    }
  }

  private def addFieldAccess(fields: Expression, expressionToDereference: Expression, structType: Struct, fieldName: String, tracker: AccessTracker): Seq[Op] = {
    injectIDField(structType, tracker)
    val call = new Invoke(
      Methods.AddFieldAccess,
      List(fields,
        new FieldMember(expressionToDereference, structType.fields.last),
        getFieldIndex(structType, fieldName)),
      None
    )
    Seq[Op](call)
  }

  def addDynamicFieldAccess(expressionToDereference: Expression, structType: Struct, fieldName: String, tracker: AccessTracker): Seq[Op] = {
    this.addFieldAccess(Commands.GetDynamicOwnedFields, expressionToDereference, structType, fieldName, tracker)
  }

  def addStaticFieldAccess(expressionToDereference: Expression, structType: Struct, fieldName: String, tracker: AccessTracker): Seq[Op] = {
    this.addFieldAccess(Vars.StaticOwnedFields, expressionToDereference, structType, fieldName, tracker)

  }

  private def addStructAccess(fields: Expression, exprToDeref: Expression, structType: Struct, tracker:AccessTracker): Op = {
    injectIDField(structType, tracker)
    new Invoke(
      Methods.AddStructAccess,
      List(fields, new Int(structType.fields.length)),
      Some(new FieldMember(exprToDeref, new StructField(structType, Names.ID, IntType)))
    )
  }

  def addDynamicStructAccess(exprToDeref: Expression, structType: Struct, tracker: AccessTracker): Op = {
    addStructAccess(Commands.GetDynamicOwnedFields, exprToDeref, structType, tracker)
  }

  def addStaticStructAccess(exprToDeref: Expression, structType: Struct, tracker: AccessTracker): Op = {
    addStructAccess(Vars.StaticOwnedFields, exprToDeref, structType, tracker)
  }
}
