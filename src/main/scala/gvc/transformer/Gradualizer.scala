package gvc.transformer
import gvc.analyzer.{LogicalOperation, ResolvedExpression, ResolvedLogical, ResolvedMethodDeclaration, ResolvedMethodDefinition, ResolvedProgram}

import scala.collection.mutable.ListBuffer
import scala.collection.{GenTraversableOnce, mutable}



object Gradualizer {

    class GradualizerException(val message: String) extends RuntimeException {
        override def getMessage(): String = message
    }

    def crossJoin[T](list: List[List[T]]): List[List[T]] = {
        list match {
            case xs :: Nil => xs map (List(_))
            case x :: xs => for {
                i <- x
                j <- crossJoin(xs)
            } yield List(i) ++ j
        }
    }

    def gradualizeResolvedProgram(resolved: ResolvedProgram): List[ResolvedProgram] = {
        println("Gradualizing the provided specification...")
        
        var permutations = List[ResolvedProgram]()
        var permutedDeclarations = permuteMethodDeclarations(resolved.methodDeclarations)
        var definitionMap = mutable.HashMap[String, ResolvedMethodDefinition]()
        resolved.methodDefinitions.foreach((defn) => {
            definitionMap += (defn.name -> defn)
        })

        permutedDeclarations.foreach(declarationSet => {
            var definitionSet = List[ResolvedMethodDefinition]()
            declarationSet.foreach((decl) => {
                val correspondingDefinition = definitionMap.get(decl.name)
                correspondingDefinition match {
                    case Some(defn: ResolvedMethodDefinition) => {
                        definitionSet = ResolvedMethodDefinition(
                            defn.parsed,
                            decl,
                            defn.body
                        ) :: definitionSet
                    }
                    case None => throw new GradualizerException("Unable to find a definition for " + decl.name)
                }
            })
            permutations = ResolvedProgram(
                declarationSet,
                definitionSet,
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
                        pre,
                        post
                    )
                    methodPermutations = duplicate :: methodPermutations
                })
            })
            println(s"${methodPermutations.length} possible specifications.")
            println(s"----------------")
            if(methodPermutations.length > 0){
                perMethodPermutations = methodPermutations :: perMethodPermutations
            }
        })
        var permutationSet = crossJoin(perMethodPermutations)
        println(s"TOTAL: ${permutationSet.length} specifications.")
        return permutationSet
    }
    
    def permuteConjunctiveClauses(expression: Option[ResolvedExpression]):List[Option[ResolvedExpression]] = {
        var permutedClauses = List[Option[ResolvedExpression]]()
        expression match {
            case Some(expr: ResolvedExpression) => {   
                val numClausesInAssertion = numClauses(expr)
                var conjunctionNodeIndices = permuteIndices(numClausesInAssertion)
                println(s"There are ${numClausesInAssertion} clauses")
                conjunctionNodeIndices.foreach(permutation => {
                    var subset = extractSubsetOfClauses(permutation, 0, expr)
                    permutedClauses = subset :: permutedClauses
                })
            }
            case None => {permutedClauses = None :: permutedClauses}
        }
        println(s"This results in ${permutedClauses.length} permutations of the assertion")

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
