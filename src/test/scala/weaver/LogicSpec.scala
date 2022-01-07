package gvc.weaver

import gvc.weaver.Logic._
import org.scalatest.funsuite.AnyFunSuite
import scala.collection.immutable.BitSet

class LogicSpec extends AnyFunSuite {
  def evaluate(formula: Disjunction, values: Set[Term]) =
    formula.conjuncts.exists(conj => conj.terms.subsetOf(values))

  def assertEquivalent(a: Disjunction, b: Disjunction) = {
    val ids = a.conjuncts.flatMap(_.terms.map(_.id)) union b.conjuncts.flatMap(_.terms.map(_.id))
    val possibilities = ids
      .subsets()
      .map(trueVars => ids.map(id => Term(id, trueVars.contains(id))))

    for (p <- possibilities) {
      assert(evaluate(a, p) == evaluate(b, p))
    }
  }

  test("contains") {
    assert(Implicant(BitSet(0, 1), BitSet()) contains Implicant(BitSet(0, 1), BitSet()))
    assert(Implicant(BitSet(3), BitSet(1, 2)) contains Implicant(BitSet(3, 2), BitSet(1)))
    assert(!(Implicant(BitSet(0, 1), BitSet()) contains(Implicant(BitSet(1), BitSet(0)))))
    assert(!(Implicant(BitSet(), BitSet(0)) contains Implicant(BitSet(2), BitSet(0))))
    assert(Implicant(BitSet(), BitSet(0, 1)) contains Implicant(BitSet(1), BitSet()))
    assert(Implicant(BitSet(), BitSet(0, 1)) contains Implicant(BitSet(0, 1), BitSet()))
  }

  test("reduce implicants 1") {
    val result = reduce(2, List(
      Implicant(BitSet(1), BitSet()),
      Implicant(BitSet(0, 1), BitSet())
    ))

    assert(result.get.toSet == Set(
      Implicant(BitSet(1), BitSet(0))
    ))
  }

  test("reduce implicants 2") {
    val result = reduce(4, List(
      Implicant(BitSet(2), BitSet()),
      Implicant(BitSet(3), BitSet()),
      Implicant(BitSet(3, 0), BitSet()),
      Implicant(BitSet(3, 1), BitSet()),
      Implicant(BitSet(3, 2), BitSet()),
      Implicant(BitSet(3, 1, 0), BitSet()),
      Implicant(BitSet(3, 2, 1), BitSet()),
      Implicant(BitSet(3, 2, 1, 0), BitSet())
    ))

    assert(result.get.toSet == Set(
      Implicant(BitSet(2), BitSet(3)),
      Implicant(BitSet(3), BitSet(0)),
      Implicant(BitSet(3), BitSet(1)),
      Implicant(BitSet(3), BitSet(2)),
      Implicant(BitSet(3, 0), BitSet(1)),
      Implicant(BitSet(3, 1), BitSet(0)),
      Implicant(BitSet(3, 1), BitSet(2)),
      Implicant(BitSet(3, 2), BitSet(1)),
      Implicant(BitSet(3, 1, 0), BitSet(2)),
      Implicant(BitSet(3, 2, 1), BitSet(0))
    ))
  }

  test("reduce implicants 3") {
    val result = reduce(4, List(
      Implicant(BitSet(2), BitSet(3)),
      Implicant(BitSet(3), BitSet(0)),
      Implicant(BitSet(3), BitSet(1)),
      Implicant(BitSet(3), BitSet(2)),
      Implicant(BitSet(3, 0), BitSet(1)),
      Implicant(BitSet(3, 1), BitSet(0)),
      Implicant(BitSet(3, 1), BitSet(2)),
      Implicant(BitSet(3, 2), BitSet(1)),
      Implicant(BitSet(3, 1, 0), BitSet(2)),
      Implicant(BitSet(3, 2, 1), BitSet(0))
    ))

    assert(result.get.toSet == Set(
      Implicant(BitSet(2), BitSet(3)),
      Implicant(BitSet(3), BitSet(1, 0)),
      Implicant(BitSet(3), BitSet(2, 1)),
      Implicant(BitSet(3, 1), BitSet(2, 0))
    ))
  }

  test("reduce irreducible") {
    assert(reduce(4, List(
      Implicant(BitSet(2), BitSet(3)),
      Implicant(BitSet(3), BitSet(1, 0)),
      Implicant(BitSet(3), BitSet(2, 1)),
      Implicant(BitSet(3, 1), BitSet(2, 0))
    )) == None)
  }

  test("reduce implicants 4") {
    assert(reduce(4, List(
      Implicant(BitSet(3), BitSet(1)),
      Implicant(BitSet(3, 2), BitSet(1))
    )).get.toSet == Set(
      Implicant(BitSet(3), BitSet(2, 1))
    ))
  }

  test("expand minterms") {
    val (a, b, c) = (Term(1), Term(2), Term(3))

    assert(computeMinterms(Array(1, 2, 3), a | !b & c) == Set(
      BitSet(0),
      BitSet(0, 1),
      BitSet(0, 1, 2),
      BitSet(0, 2),
      BitSet(2)
    ))

    assert(computeMinterms(Array(1, 2, 3), a & b | b) == Set(
      BitSet(1),
      BitSet(0, 1),
      BitSet(0, 1, 2),
      BitSet(1, 2)
    ))

    assert(computeMinterms(Array(), Disjunction()) == Set.empty)
  }

  test("simplify 1") {
    val (a, b) = (Term(1), Term(2))
    val input = a & !b | !a
    val result = simplify(input)
    assertEquivalent(input, result)
    assert(result == (!a | !b))
  }

  test("simplify 2") {
    // Test case pulled from https://en.wikipedia.org/wiki/Petrick%27s_method#Example_of_Petrick's_method

    // Minterms 0, 1, 2, 5, 6, 7
    //        = 000 | 001 | 010 | 101 | 110 | 111
    //        = !a!b!c | !a!bc | !ab!c | a!bc | ab!c | abc

    val (a, b, c) = (Term(1), Term(2), Term(3))
    val input =
      !a & !b & !c |
      !a & !b & c |
      !a & b & !c |
      a & !b & c |
      a & b & !c |
      a & b & c

    val result = simplify(input)

    assertEquivalent(input, result)

    assert(result == (!a & !b | b & !c | a & c))
    // Could also be !a & !c | !b & c | a & b
  }

  test("simplify true") {
    // True is an empty conjunction
    val (a, b) = (Term(123), Term(-1))
    val t = Conjunction()
    val input = (a & b) | t

    val result = simplify(input)
    assertEquivalent(input, result)

    assert(result == Disjunction(t))
  }

  test("simplify contradiction") {
    // False is an empty disjunction
    val (a, b) = (Term(123), Term(1))
    val input = a & !a | b & !b
    val result = simplify(input)

    assertEquivalent(input, result)
    assert(result == Disjunction())
  }

  test("simplify already simplified") {
    val (a, b) = (Term(123), Term(-1))
    val input = a | !b
    assert(simplify(a | !b) == (a | !b))
    assert(simplify(Disjunction(a & b)) == Disjunction(a & b))
  }

  test("simplify all three-variable formulas with true terms") {
    val (a, b, c) = (Term(1), Term(2), Term(3))
    val possibleTerms = Set(a, b, c)

    // Size: 2^3 = 8
    val possibleConjuncts = possibleTerms.subsets().map(c => Conjunction(c)).toSet
    // Size: 2^8 = 256
    val possibleDisjuncts = possibleConjuncts.subsets().map(conjuncts => Disjunction(conjuncts))

    for (input <- possibleDisjuncts) {
      val result = simplify(input)
      assertEquivalent(input, result)
      assert(result.conjuncts.size <= input.conjuncts.size)
    }
  }

  test("simplify all three-variable formulas with terms of two variables") {
    val (a, b, c) = (Term(1), Term(2), Term(3))
    val possibleTerms = Set(a, b, c, !a, !b, !c)

    // Size: 6 choose 2 = 15
    val possibleConjuncts = possibleTerms.subsets(2).map(c => Conjunction(c)).toSet
    // Size: 2^15 = 32,768
    val possibleDisjuncts = possibleConjuncts.subsets().map(conjuncts => Disjunction(conjuncts))

    // This takes a few seconds to compute
    for (input <- possibleDisjuncts) {
      val result = simplify(input)
      assertEquivalent(input, result)

      // Verify that it actually does result in fewer conjuncts
      assert(result.conjuncts.size <= input.conjuncts.size)
    }
  }
}