package gvc.transformer
import gvc.analyzer.ResolvedProgram
import gvc.analyzer.ResolvedMethodDeclaration
import scala.collection.mutable.ListBuffer
import gvc.analyzer.ResolvedLogical
import gvc.analyzer.LogicalOperation
import gvc.analyzer.ResolvedExpression
import scala.collection.GenTraversableOnce



object Gradualizer {

    def crossJoin[T](list: List[List[T]]): List[List[T]] =
        list match {
            case xs :: Nil => xs map (List(_))
            case x :: xs => for {
                i <- x
                j <- crossJoin(xs)
            } yield List(i) ++ j
        }

    def gradualizeResolvedProgram(resolved: ResolvedProgram): List[ResolvedProgram] = {
        println("Gradualizing the provided specification...")
        
        var permutations = List[ResolvedProgram]()
        var declarations = List()
        var definitions = List()

        var permutedDeclarations = permuteMethodDeclarations(resolved.methodDeclarations)

        permutedDeclarations.foreach(declarationSet => {
            permutations = ResolvedProgram(
                declarationSet,
                resolved.methodDefinitions,
                resolved.predicateDeclarations,
                resolved.predicateDefinitions,
                resolved.structDefinitions,
                resolved.types
            ) :: permutations
        })
        return permutations
    }

    def permuteMethodDeclarations(declarations: List[ResolvedMethodDeclaration]): List[List[ResolvedMethodDeclaration]] = {
        var perMethodPermutations = List[List[ResolvedMethodDeclaration]]()
        
        declarations.foreach(decl => {
            println(s"Permuting method: ${decl.name}")

            var permutedPreconditions = permuteConjunctiveClauses(decl.precondition)
            println(s"${permutedPreconditions.length} combination(s) of preconditions")

            var permutedPostconditions = permuteConjunctiveClauses(decl.postcondition)
            println(s"${permutedPostconditions.length} combination(s) of postconditions")

            var methodPermutations = List[ResolvedMethodDeclaration]()

            permutedPostconditions.foreach(post => {
                permutedPreconditions.foreach(pre => {
                    var duplicate = new ResolvedMethodDeclaration(
                        decl.parsed,
                        decl.returnType,
                        decl.name,
                        decl.arguments,
                        Some(pre),
                        Some(post)
                    )
                    methodPermutations = duplicate :: methodPermutations
                })
            })
            println(s"${permutedPostconditions.length} possible specifications.")
            println(s"----------------")
            if(methodPermutations.length > 0){
                perMethodPermutations = methodPermutations :: perMethodPermutations
            }
        })
        var permutationSet = crossJoin(perMethodPermutations)
        println(s"TOTAL: ${permutationSet.length} specifications.")
        return permutationSet
    }
    
    def permuteConjunctiveClauses(condition: Option[ResolvedExpression]):List[ResolvedExpression] = {
        var permutedClauses = List[ResolvedExpression]()
        condition match {
            case Some(expr: ResolvedExpression) => {   
                var conjunctionNodeIndices = permuteIndices(numClauses(expr))
                conjunctionNodeIndices.foreach(permutation => {
                    var subset = extractSubsetOfClauses(permutation, 0, expr)
                    subset match {
                        case Some(validSubset: ResolvedExpression) => {permutedClauses = validSubset :: permutedClauses}
                        case None => {}
                    }
                })
            }
            case None => {}
        }
        return permutedClauses
    }

    def extractSubsetOfClauses(subset: List[Int], currentIndex:Int, root:ResolvedExpression):Option[ResolvedExpression] = {
        if(subset.length > 0) {
            root match {
                case resolveRoot: ResolvedLogical => {
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
