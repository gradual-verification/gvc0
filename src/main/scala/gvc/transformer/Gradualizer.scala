package gvc.transformer

import gvc.analyzer.ResolvedProgram
import gvc.analyzer.ResolvedMethodDeclaration
import gvc.analyzer.ResolvedMethodDefinition
import scala.collection.mutable.ListBuffer
import gvc.analyzer.ResolvedLogical
import gvc.analyzer.LogicalOperation
import gvc.analyzer.ResolvedExpression
import gvc.analyzer.ResolvedImprecision

object Gradualizer {
    def gradualizeResolvedProgram(resolved: ResolvedProgram): List[ResolvedProgram] = {
        var permutations = List[ResolvedProgram]()
        var declarations = List()
        var definitions = List()

        var permutedDeclarations = permute(resolved.methodDeclarations)

        resolved.methodDeclarations.foreach((decl: ResolvedMethodDeclaration) => {
            
            
            decl.postcondition match {
                case Some(expr: ResolvedExpression) => {   
                    var permutations = permuteIndices(numClauses(expr))
                    permutations.foreach(perm => {
                        println(perm)
                        println(extractSubsetOfClauses(perm, 0, expr))
                        println("--------")
                    })
                }
                case Some(ResolvedImprecision(_)) => {
                    
                }
                case None => {
                    
                }
            }
            decl.precondition match {
                case Some(expr: ResolvedExpression) => {   
                    var permutations = permuteIndices(numClauses(expr))
                    permutations.foreach(perm => {
                        extractSubsetOfClauses(perm, 0, expr)
                    })
                }
                case Some(impr: ResolvedImprecision) => {
                    
                }
                case None => {
                    
                }
            }
        })

        return permutations
    }

    def extractSubsetOfClauses(subset: List[Int], currentIndex:Int, root:ResolvedExpression):Option[ResolvedExpression] = {
        if(subset.length > 0) {
            root match {
                case resolveRoot: ResolvedLogical => {
                    println(subset(subset.length - 1))
                    if(subset(subset.length - 1) == currentIndex){
                        var left = extractSubsetOfClauses(subset.slice(0, subset.length - 1), currentIndex + 1, resolveRoot.left)
                        left match {
                            case Some(leftExists: ResolvedExpression) => {
                                return Some(ResolvedLogical(resolveRoot.parsed, leftExists, resolveRoot.right, resolveRoot.operation))
                            }
                            case None => {
                                return Some(resolveRoot.right)
                            }
                        }
                    }else{
                        return extractSubsetOfClauses(subset, currentIndex + 1, resolveRoot.left)
                    }
                }
                case resolveRoot:ResolvedExpression => {
                    if(subset(subset.length - 1) == currentIndex){
                        return Some(root)
                    }else{
                        return None
                    }
                }
            }
        }else{
            return None
        }
    } 
    
    def permute[T](space: List[T]):ListBuffer[List[T]] = {
        var collection = ListBuffer[List[T]]()
        permuteRecurse(space, collection, List(), 0)
        return collection
    }

    def permuteIndices(max: Int):ListBuffer[List[Int]] = {
        var collection = ListBuffer[List[Int]]()
        permuteIndexRecurse(max, collection, List(), 0)
        return collection        
    }

    //https://stackoverflow.com/a/8171776
    def permuteRecurse[T](space: List[T], collection:ListBuffer[List[T]], current:List[T], index: Int):Unit = {
        if(index == space.length){
            collection += current
        }else{
            permuteRecurse(space, collection, space(index) :: current, index + 1)
            permuteRecurse(space, collection, current, index + 1)
        }
    }

    def permuteIndexRecurse(max: Int, collection:ListBuffer[List[Int]], current:List[Int], index: Int): Unit = {
        if(index == max){
            collection += current
        }else{
            permuteIndexRecurse(max, collection, index :: current, index + 1)
            permuteIndexRecurse(max, collection, current, index + 1)
        }        
    }   

    def numClauses(expr: ResolvedExpression):Int = {
        var currNode = expr
        var numClauses = 1
        if(expr.isInstanceOf[ResolvedLogical]){
            var asLogical = currNode.asInstanceOf[ResolvedLogical]
            while((asLogical.operation eq LogicalOperation.And) && asLogical.left.isInstanceOf[ResolvedLogical]){
                numClauses += 1
                asLogical = asLogical.left.asInstanceOf[ResolvedLogical]
            }
        }
        return numClauses
    }
}
