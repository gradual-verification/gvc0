# Adding Line and Column Numbers to the IR

Every `gvc.parser.Node` has a field `span: SourceSpan`, which stores the
`SourcePosition` (line and column number) where the node starts, and the
`SourcePosition` where the node ends. Every `gvc.analyzer.ResolvedNode`
has a field `parsed` that refers back to the `Node` that produced this
resolved node.

The following classes (but not traits) in `gvc.transformer.IR`, except
for `Var` & `Parameter`, have a new field `resolved: ResolvedNode` added
to them. This field refers to the resolved node that produced this IR Op
or Expression. When the GVC0 IR is converted to the Silver IR, the
`resolved` field is used to build the source position information in the
Silver IR. The Silver IR nodes' `pos: Position` field contain a
`viper.silver.ast.TranslatedPosition` object wrapping a
`viper.silver.ast.SourcePosition`. A `SourcePosition` object stores
the start position in field `start: viper.silver.ast.LineColumnPosition`
and the end position in field
`end: Option[viper.silver.ast.LineColumnPosition]`.

- trait `Expression`
    - `Var`*
        - `Parameter`*
    - trait `Member`
        - `FieldMember`
        - `DereferenceMember`
        - `ArrayMember`
    - trait `SpecificationExpression`
        - `Accessibility`
        - `PredicateInstance`
        - `Result`
        - `Imprecise`
    - trait `Literal`
        - `IntLit`
        - `CharLit`
        - `BoolLit`
        - `StringLit`
        - `NullLit`
    - `Conditional`
    - `Binary`
    - `Unary`

- trait `Op`
    - `Invoke`
    - `AllocValue`
    - `AllocStruct`
    - `AllocArray`
    - `Assign`
    - `AssignMember`
    - `Assert`
    - `Fold`
    - `Unfold`
    - `Error`
    - `Return`
    - `If`
    - `While`

The `resolved` field cannot be added to `Var` and `Parameter` because
the same `Var` or `Parameter` is reused multiple times in the IR.
Changing this design decision would require a substantial refactoring of
the `gvc.transformer` package.

Currently, the additions to the IR are not very elegant: in each subtype
of `gvc.transformer.IR.Expression` and `gvc.transformer.IR.Op`, the
`resolved` field is of type `gvc.analyzer.ResolvedNode` rather than a
more specific subtype of `ResolvedNode`. This is because each
`ResolvedNode` can produce more than one IR Op or Expression, and so the
`resolved` field in an IR Op or Expression could refer to resolved nodes
of different types. Furthermore, each `resolved` field has a dummy
default value of `Zilch`, because the IR nodes are constructed in tests.
Removing this dummy default value would require a further refactoring.