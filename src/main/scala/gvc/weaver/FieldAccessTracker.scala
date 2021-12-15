package gvc.weaver
import gvc.transformer.IRGraph._
import scala.collection.mutable

object FieldAccessInterface {
  val INIT_OWNED_FIELDS = new Method(
    "initOwnedFields",
    Some(BoolType),
    None,
    None
  )

  val ADD_FIELD_ACCESS = new Method(
    "addAccess",
    Some(BoolType),
    None,
    None
  )

  val MERGE = new Method(
    "merge",
    Some(BoolType),
    None,
    None,
  )

  val ASSERT_ACC = new Method(
    "assertAcc",
    Some(BoolType),
    None,
    None,
  )

  val ADD_STRUCT_ACCESS = new Method(
      "addStructAccess",
    Some(IntType),
    None,
    None
  )

  val INSTANCE_COUNTER = "_instance_counter"
  val ID = "_id"
  // TODO: Replace by hard-coded implementation or parse fieldaccess.c0
  val OWNED_FIELDS_STRUCT = new Struct("OwnedFields")
}

object FieldAccessTracker {
  val OwnedFields = {}

  def injectAccessTracking(ir: Program): Unit = {
  
  }

  def getOwnedFieldsVar(counter: Integer): Var = {
    new Var(new ReferenceType(FieldAccessInterface.OWNED_FIELDS_STRUCT), "fields_" + counter.toString())
  }

  def getFieldIndex(structType: Struct, fieldName: String): Int = {
    val index = structType.fields.indexWhere((field) => field.name.equals(fieldName))
    new Int(index)
  }

  def initializeInstanceCounter(): mutable.ArrayBuffer[Op] = {
    val instanceCounterVar = new Var(new PointerType(IntType), FieldAccessInterface.INSTANCE_COUNTER)
    val alloc = new AllocValue(IntType, instanceCounterVar)
    val assign = new AssignMember(new DereferenceMember(instanceCounterVar, IntType), new Int(0))
    mutable.ArrayBuffer[Op](alloc, assign)
  }

  def createOwnedFields(counter: Integer): mutable.ArrayBuffer[Op] = {
    val fieldsVar = getOwnedFieldsVar(counter)
    val alloc = new AllocStruct(
      FieldAccessInterface.OWNED_FIELDS_STRUCT,
      fieldsVar
    )
    val init = new Invoke(FieldAccessInterface.INIT_OWNED_FIELDS, List(fieldsVar), None)
    mutable.ArrayBuffer[Op](alloc, init)
  }

  def assertFieldAccess(counter: Integer, expressionToDereference: Expression, structType: Struct, fieldName: String): mutable.ArrayBuffer[Op] = {
    val ownedFieldsVar = getOwnedFieldsVar(counter)
    val call = new Invoke(FieldAccessInterface.ASSERT_ACC, List(ownedFieldsVar, new FieldMember(expressionToDereference, structType.fields.last), getFieldIndex(structType, fieldName)), None)
    mutable.ArrayBuffer[Op](call)
  }

  def mergeFields(targetCounter: Integer, sourceCounter:Integer): mutable.ArrayBuffer[Op] = {
    val targetVar = getOwnedFieldsVar(targetCounter)
    val sourceVar = getOwnedFieldsVar(sourceCounter)
    val call = new Invoke(FieldAccessInterface.MERGE, List(targetVar, sourceVar), None)
    mutable.ArrayBuffer[Op](call)
  }

  def addFieldAccess(fieldsCounter: Integer, expressionToDereference:Expression, structType:Struct, fieldName: String): mutable.ArrayBuffer[Op] = {
    val call = new Invoke(
      FieldAccessInterface.ADD_FIELD_ACCESS,
      List(getOwnedFieldsVar(fieldsCounter),
        new FieldMember(expressionToDereference, structType.fields.last),
        getFieldIndex(structType, fieldName)),
      None
    )
    mutable.ArrayBuffer[Op](call)
  }

  def addStructAccess(fieldsCounter: Integer, structType: Struct): mutable.ArrayBuffer[Op] = {
    val call = new Invoke(
      FieldAccessInterface.ADD_FIELD_ACCESS,
      List(getOwnedFieldsVar(fieldsCounter), new Int(structType.fields.length)),
      None
    )
    mutable.ArrayBuffer[Op](call)
  }
}