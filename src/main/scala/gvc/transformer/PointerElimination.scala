package gvc.transformer
import scala.collection.mutable

// Rewrites all bare pointers to instead be single-field structs
object PointerElimination {
  def transform(program: IR.Program): Unit = {
    val c = new Converter(program)

    def convertMember(m: IR.Member): IR.Member = m match {
      case _: IR.ArrayMember => arraysUnsupported
      case d: IR.DereferenceMember => c.dereference(convert(d.root), d)
      case f: IR.FieldMember => new IR.FieldMember(convert(f.root), f.field, f.resolved)
    }

    def convert(expr: IR.Expression): IR.Expression = expr match {
      case a: IR.Accessibility => new IR.Accessibility(convertMember(a.member), a.resolved)
      case b: IR.Binary => new IR.Binary(b.operator, convert(b.left), convert(b.right), b.resolved)
      case c: IR.Conditional => new IR.Conditional(convert(c.condition), convert(c.ifTrue), convert(c.ifFalse), c.resolved)
      case i: IR.Imprecise => new IR.Imprecise(i.precise.map(convert), i.resolved)
      case m: IR.Member => convertMember(m)
      case p: IR.PredicateInstance => new IR.PredicateInstance(p.predicate, p.arguments.map(convert), p.resolved)
      case r: IR.Result => new IR.Result(r.method, r.resolved)
      case u: IR.Unary => new IR.Unary(u.operator, convert(u.operand), u.resolved)
      case v: IR.Var => v
      case l: IR.Literal => l
    }

    def convertBlock(block: IR.Block): Unit = {
      for (op <- block.toList) convertOp(op)
    }

    def convertOp(op: IR.Op): Unit = op match {
      case _: IR.AllocArray => arraysUnsupported
      case a: IR.AllocStruct => a.target = convert(a.target)
      case a: IR.AllocValue =>
        a.insertBefore(new IR.AllocStruct(c.lookup(a.valueType), a.target))
        a.remove()
      case a: IR.Assert => a.value = convert(a.value)
      case a: IR.Assign => a.value = convert(a.value);
      case a: IR.AssignMember =>
        a.value = convert(a.value)
        a.member = convertMember(a.member)
      case e: IR.Error =>
        e.value = convert(e.value)
      case f: IR.Fold =>
        f.instance.arguments = f.instance.arguments.map(convert)
      case i: IR.If =>
        i.condition = convert(i.condition)
        convertBlock(i.ifTrue)
        convertBlock(i.ifFalse)
      case i: IR.Invoke =>
        i.arguments = i.arguments.map(convert)
        i.target = i.target.map(convert)
      case r: IR.Return =>
        r.value = r.value.map(convert)
      case u: IR.Unfold =>
        u.instance.arguments = u.instance.arguments.map(convert)
      case w: IR.While =>
        w.condition = convert(w.condition)
        w.invariant = convert(w.invariant)
        convertBlock(w.body)
    }

    // Create an immutable snapshot of the current structs since
    // conversion may add structs
    val originalStructs = program.structs.toList

    // Convert all operations/expressions first, so that the underlying types
    // are all preserved until all expressions are rewritten
    for (method <- program.methods) {
      convertBlock(method.body)
      method.precondition = method.precondition.map(convert)
      method.postcondition = method.postcondition.map(convert)
    }

    for (pred <- program.predicates) {
      pred.expression = convert(pred.expression)
    }

    // After all expressions are rewritten, update all the types

    for (struct <- originalStructs) {
      for (field <- struct.fields) {
        field.valueType = c.convert(field.valueType)
      }
    }

    for (method <- program.methods) {
      for (p <- method.parameters)
        p.varType = c.convert(p.varType)
      for (v <- method.variables)
        v.varType = c.convert(v.varType)

      method.returnType = method.returnType.map(c.convert(_))
    }

    for (pred <- program.predicates) {
      for (p <- pred.parameters)
        p.varType = c.convert(p.varType)
    }
  }

  private class Converter(program: IR.Program) {
    val structs = mutable.Map[String, IR.StructDefinition]()

    def lookup(valueType: IR.Type): IR.StructDefinition = {
      structs.getOrElseUpdate(valueType.name, {
        val struct = program.newStruct("_ptr_" + valueType.name.replace(' ', '_').replace('*', '_'))
        struct.addField("value", convert(valueType))
        struct
      })
    }

    def pointerType(pointer: IR.PointerType): IR.ReferenceType = {
      new IR.ReferenceType(lookup(pointer.valueType))
    }

    def dereference(root: IR.Expression, deref: IR.DereferenceMember): IR.FieldMember = {
      val t = deref.valueType.getOrElse(throw new TransformerException(s"Invalid pointer dereference for ${deref.root.valueType}"))
      new IR.FieldMember(root, lookup(t).fields.head, deref.resolved)
    }

    def convert(t: IR.Type) = t match {
      case _: IR.ArrayType | _: IR.ReferenceArrayType => arraysUnsupported
      case ptr: IR.PointerType => pointerType(ptr)
      case value => value
    }
  }

  private def arraysUnsupported: Nothing =
    throw new TransformerException("Arrays are not supported")
}