# Pipeline

1. C0 goes to the parser, which produces an AST
2. The resolver and type checker check the AST
3. The IR Transformer builds the IR
4. IRSilver translates the IR into silver
5. Silicon verifies as much silver as it can
6. The weaver inserts runtime checks
7. IRPrinter prints the IR as C0
8. cc0 compiles that C0 with runtime.c0

# Inside Parser

## AST representation

Fractional permissions are stored as nodes using AccessibilityExpression
from parser/AST.scala:39 definition. 

## Parsing 

Parser/Expressions.scala defines the grammer rules that parse a
fractional permission from 'acc' keywords 
and stores them in an AccessibilityExpression permission field.

# Inside Analyzer

## Resolved AST

Analyzer/Expressions.scala:87 defines ResolvedAccessibility, allowing 
its value type to be defined as boolean for the type checker

## Conversion

Under analyzer/Resolver.scala:679, AccessibilityExpression is turned
into ResolvedAccessibility for the Resolved AST, reporting any errors 
if they exist

## Type Check

analyzer/TypeChecker:291 will ensure that the field under 'acc' is a field 
by calling assertField and then assertPermissionExpression to ensure that the 
field contains a valid permission


AssertField is defined at analyzer/TypeChecker:320, which if the field is a
variable or a \result, then it errors out, otherwise is calls assertFieldInner
in a catch all under match

AssertFieldInner is defined at analyzer/TypeChecker:328 and is a recursive function
that walks through from fields back to their parents to verify them all.

AssertPermissonExpression is defined at analyzer/TypeChecker:337 and ensures
that the provided permission is valid.

## Validation

analyzer/Validator:19-22 runs validation on the program after the typer checker
finds no errors

# Inside IR

## Resolved tree to IR

transformer/IRTransofmrer:566 takes Resolved Accessibility nodes to IR representation

