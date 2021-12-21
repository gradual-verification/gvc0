package gvc.weaver
import gvc.transformer.IRGraph
import gvc.transformer.IRGraph._
import viper.silicon.state.CheckInfo
import viper.silver.ast.{FieldAccess, LocalVar}

import scala.collection.mutable

object AccessChecks{

  private object Names {
    val NM_INSTANCE_COUNTER = "_instance_counter"
    val NM_DYN_OWNED_FIELDS = "dyn_fields"
    val NM_ID = "_id"
  }
  private object Structs {
    val ST_OWNED_FIELDS = new Struct("OwnedFields")
  }
  private object Vars {
    val VAR_INSTANCE_COUNTER = new Var(new PointerType(IntType), Names.NM_INSTANCE_COUNTER)
    val VAR_STATIC_OWNED_FIELDS = new Var(new ReferenceType(Structs.ST_OWNED_FIELDS), "static_fields")
    val VAR_DYN_OWNED_FIELDS = new Var(new ReferenceArrayType(Structs.ST_OWNED_FIELDS), name=Names.NM_DYN_OWNED_FIELDS)
  }
  private object Methods{
    val MT_INIT_OWNED_FIELDS = new Method(
      "initOwnedFields",
      Some(BoolType),
      None,
      None
    )
    val MT_ADD_FIELD_ACCESS = new Method(
      "addAccess",
      Some(BoolType),
      None,
      None
    )
    val MT_ASSERT_ACC = new Method(
      "assertAcc",
      Some(BoolType),
      None,
      None,
    )
    val MT_ASSERT = new Method(
      "assertAccess",
      Some(BoolType),
      None,
      None,
    )
    val MT_ASSERT_DISJOINT = new Method(
      "assertDisjointAccess",
      Some(BoolType),
      None,
      None,
    )

    val MT_ADD_STRUCT_ACCESS = new Method(
      "addStructAccess",
      Some(IntType),
      None,
      None
    )
    val MT_JOIN = new Method(
      "disjoin",
      Some(BoolType),
      None,
      None,
    )
    val MT_DISJOIN = new Method(
      "disjoin",
      Some(BoolType),
      None,
      None,
    )
  }
  private object Commands {
    val CMD_INIT_COUNTER = Seq(
      new AllocValue(IntType, Vars.VAR_INSTANCE_COUNTER),
      new AssignMember(new DereferenceMember(Vars.VAR_INSTANCE_COUNTER, IntType), new Int(0))
    )
    val CMD_INIT_STATIC = Seq(
      new AllocStruct(Structs.ST_OWNED_FIELDS, Vars.VAR_STATIC_OWNED_FIELDS),
      new Invoke(Methods.MT_INIT_OWNED_FIELDS, List(Vars.VAR_STATIC_OWNED_FIELDS, Vars.VAR_INSTANCE_COUNTER), None)
    )
    val CMD_INIT_DYN = Seq(
      new AllocArray(new ReferenceType(Structs.ST_OWNED_FIELDS), new Int(1), Vars.VAR_DYN_OWNED_FIELDS),
      new AllocStruct(Structs.ST_OWNED_FIELDS, new ArrayAtIndex(Vars.VAR_DYN_OWNED_FIELDS, Vars.VAR_DYN_OWNED_FIELDS.valueType, new Int(0))),
      new Invoke(Methods.MT_INIT_OWNED_FIELDS, List(Commands.CMD_GET_DYN_OWNED_FIELDS, Vars.VAR_INSTANCE_COUNTER), None),
    )
    val CMD_JOIN = new Invoke(Methods.MT_JOIN, List(Commands.CMD_GET_DYN_OWNED_FIELDS, Vars.VAR_STATIC_OWNED_FIELDS), None)
    val CMD_DISJOIN = new Invoke(Methods.MT_DISJOIN, List(Commands.CMD_GET_DYN_OWNED_FIELDS, Vars.VAR_STATIC_OWNED_FIELDS), None)
    val CMD_GET_DYN_OWNED_FIELDS = new ArrayAtIndex(Vars.VAR_DYN_OWNED_FIELDS, new ReferenceType(Structs.ST_OWNED_FIELDS), new Int(0))

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

  case class CallGraphEdge(var callsImprecise: Boolean, callsites: mutable.ArrayBuffer[AtOp], returns: mutable.ArrayBuffer[AtOp])
  class CallGraph {
    var graph: Map[Method, CallGraphEdge] = Map[Method, CallGraphEdge]()
    var entry: Option[Method] = None
    def setEntry(method: Method): Unit = {
      entry = Some(method)
    }
    def addEdge(calledMethod: Method, callPosition: AtOp): Unit = {
      if (graph isDefinedAt calledMethod) {
        graph(calledMethod).callsites += callPosition
      } else {
        val edge = CallGraphEdge(callsImprecise = false, mutable.ArrayBuffer[AtOp](callPosition), mutable.ArrayBuffer[AtOp]())
        graph += calledMethod -> edge
      }
      if (isImprecise(calledMethod)) {
        if (!(graph isDefinedAt callPosition.method)) {
          graph += callPosition.method -> CallGraphEdge(callsImprecise = true, mutable.ArrayBuffer[AtOp](), mutable.ArrayBuffer[AtOp]())
        } else {
          graph(callPosition.method).callsImprecise = true
        }
      }
    }
    def addReturn(returnPosition: AtOp): Unit ={
      if(graph isDefinedAt returnPosition.method){
        graph(returnPosition.method).returns += returnPosition
      }else{
        graph += returnPosition.method -> CallGraphEdge(callsImprecise = false, mutable.ArrayBuffer[AtOp](), mutable.ArrayBuffer[AtOp](returnPosition))
      }
    }
  }

  var visited: Set[Method] = Set[Method]()
  var visitedStructs: Set[Struct] = Set[Struct]()
  var allocations: Set[AtOp] = Set[AtOp]()

  def injectSupport(ir: Program, callGraph: CallGraph): Unit = {
    if (visited.nonEmpty) {
      for ((method: Method, edge: CallGraphEdge) <- callGraph.graph) {
        injectParameters(method, edge)
        edge.callsites.foreach((position: AtOp) => {
          if(optionImprecise(method.precondition)) {
            position.insertBefore(Commands.CMD_JOIN)
          }
          if (optionImprecise(method.postcondition)) {
            position.insertAfter(Commands.CMD_DISJOIN)
          }
        })
      }
      allocations.foreach(alloc => {
        val allocationOp = alloc.block.ops(alloc.index)
        allocationOp match {
          case structAlloc: AllocStruct =>
            if(isImprecise(alloc.method)){
              injectIDField(structAlloc.struct)
              alloc.insertAfter(addDynamicStructAccess(structAlloc.target, structAlloc.struct))
            }else{
              //assign and increment _id_counter
            }
        }
      })
      callGraph.entry match {
        case Some(mainMethod) =>
          var currBlock = mainMethod.entry
          while (currBlock.previous.isDefined) {
            currBlock = currBlock.previous.get.asInstanceOf[BasicBlock]
          }
          mainMethod.addExistingVar(Vars.VAR_INSTANCE_COUNTER)
          currBlock.ops = mutable.ArrayBuffer(Commands.CMD_INIT_COUNTER ++ mainMethod.entry.ops: _*)
      }
    }
  }

  def injectParameters(method: Method, edge:CallGraphEdge): Unit = {
    if (isImprecise(method)) {
      method.addParameter(new PointerType(new ReferenceArrayType(Structs.ST_OWNED_FIELDS)), Names.NM_DYN_OWNED_FIELDS)
      generateStaticTracker(method)
      if (method.postcondition.isDefined && !optionImprecise(method.postcondition)) {
        for (ret <- edge.returns) {
          ret.insertBefore(new AssignIndex(Vars.VAR_DYN_OWNED_FIELDS, new Int(0), Vars.VAR_STATIC_OWNED_FIELDS))
        }
      }
    } else {
      method.addParameter(new PointerType(IntType), Names.NM_INSTANCE_COUNTER)
      if (edge.callsImprecise) {
        method.addExistingVar(Vars.VAR_DYN_OWNED_FIELDS)
        method.entry.ops = mutable.ArrayBuffer(Commands.CMD_INIT_DYN ++ method.entry.ops: _*)
      }
    }
  }

  def generateStaticTracker(method: Method): Unit = {
    var staticFieldInitialization = Seq[Op]()
    val accessibilityPredicates = collectStaticPermissions(method.precondition)
    accessibilityPredicates.foreach(acc => {
      acc.member match {
        case member: FieldMember =>
          staticFieldInitialization = staticFieldInitialization ++ addFieldAccess(
            Vars.VAR_STATIC_OWNED_FIELDS,
            member.root,
            member.field.struct,
            member.field.name
          )
        case _: DereferenceMember => throw new WeaverException("Field access check implementation doesn't exist for DereferenceMember.")
      }
    })
    method.addExistingVar(Vars.VAR_STATIC_OWNED_FIELDS)
    method.entry.ops = mutable.ArrayBuffer(Commands.CMD_INIT_STATIC ++ staticFieldInitialization ++ method.entry.ops: _*)
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

  def injectIDField(structType: Struct): Unit = {
    if (!visitedStructs.contains(structType)) {
      structType.addField(Names.NM_ID, IntType)
      visitedStructs += structType
    }
  }

  def generateAccessCheck(info: CheckInfo, loc: FieldAccess, toDeref: Expression, structType: Struct, fieldName: String): Seq[Op] = {
    injectIDField(structType)
    if (info.overlaps && !isStaticallyVerifiedField(loc)) {
      Seq(new Invoke(
        Methods.MT_ASSERT_DISJOINT,
        List(Vars.VAR_STATIC_OWNED_FIELDS,
          Commands.CMD_GET_DYN_OWNED_FIELDS,
          new FieldMember(toDeref, structType.fields.last),
          getFieldIndex(structType, fieldName)),
        None
      ))
    } else {
      Seq(new Invoke(
        Methods.MT_ASSERT,
        List(Commands.CMD_GET_DYN_OWNED_FIELDS,
          new FieldMember(toDeref, structType.fields.last),
          getFieldIndex(structType, fieldName)),
        None
      ))
    }
  }

  def isStaticallyVerifiedField(loc: FieldAccess): Boolean = {
    true
  }

  def assertFieldAccess(info: viper.silicon.state.CheckInfo, loc: FieldAccess, method: Method): Seq[Op] = {
    val fieldName = loc.field.name.substring(loc.field.name.lastIndexOf('$') + 1)
    loc.rcv match {
      case LocalVar(name, _) =>
        method.getVar(name) match {
          case Some(variable) =>
            val structType = variable.valueType.asInstanceOf[ReferenceType].struct
            generateAccessCheck(info, loc, variable, structType, fieldName)
          case None => ???
        }
      case _ => ???
    }
  }

  private def addFieldAccess(fields: Expression, expressionToDereference: Expression, structType: Struct, fieldName: String): Seq[Op] = {
    injectIDField(structType)
    val call = new Invoke(
      Methods.MT_ADD_FIELD_ACCESS,
      List(fields,
        new FieldMember(expressionToDereference, structType.fields.last),
        getFieldIndex(structType, fieldName)),
      None
    )
    Seq[Op](call)
  }

  def addDynamicFieldAccess(expressionToDereference: Expression, structType: Struct, fieldName: String): Seq[Op] = {
    this.addFieldAccess(Commands.CMD_GET_DYN_OWNED_FIELDS, expressionToDereference, structType, fieldName)
  }

  def addStaticFieldAccess(expressionToDereference: Expression, structType: Struct, fieldName: String): Seq[Op] = {
    this.addFieldAccess(Vars.VAR_STATIC_OWNED_FIELDS, expressionToDereference, structType, fieldName)

  }

  private def addStructAccess(fields: Expression, exprToDeref: Expression, structType: Struct): Op = {
    injectIDField(structType)
    new Invoke(
      Methods.MT_ADD_STRUCT_ACCESS,
      List(fields, new Int(structType.fields.length)),
      Some(new FieldMember(exprToDeref, new StructField(structType, Names.NM_ID, IntType)))
    )

  }

  def addDynamicStructAccess(exprToDeref: Expression, structType: Struct): Op = {
    addStructAccess(Commands.CMD_GET_DYN_OWNED_FIELDS, exprToDeref, structType)
  }

  def addStaticStructAccess(exprToDeref: Expression, structType: Struct): Op = {
    addStructAccess(Vars.VAR_STATIC_OWNED_FIELDS, exprToDeref, structType)
  }
}
