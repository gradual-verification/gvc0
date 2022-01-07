package gvc.weaver

import scala.collection.immutable.SortedSet
import scala.collection.mutable
import scala.collection.immutable.BitSet

// Implementation of Quine-McCluskey algorithm and Petrick's method
object Logic {

  // Structures to represent terms, conjunctions, and disjunctions, with utility methods to make
  // testing easier

  case class Term(val id: Integer, val value: Boolean = true) {
    def unary_! = Term(id, !value)
    def &(other: Term): Conjunction = Conjunction(this, other)
    def &(other: Conjunction) = Conjunction(other.terms + this)
    def |(other: Term) = Disjunction(Conjunction(this), Conjunction(other))
    def |(other: Conjunction) = Disjunction(Conjunction(this), other)
    def |(other: Disjunction) = Disjunction(other.conjuncts + Conjunction(this))
    override def toString() = if (value) id.toString() else "!" + id.toString()
  }
  object Term {
    implicit def ordering: Ordering[Term] = Ordering.by(t => (t.id, t.value))
  }

  case class Conjunction(terms: Set[Term]) {
    def &(other: Term): Conjunction = Conjunction(terms + other)
    def &(other: Conjunction) = Conjunction(terms ++ other.terms)
    def |(term: Term) = Disjunction(this, Conjunction(term))
    def |(other: Conjunction) = Disjunction(this, other)
    def |(other: Disjunction) = Disjunction(other.conjuncts + this)
    override def toString() =
      if (terms.isEmpty) "true"
      else "(" + terms.toSeq.sorted.mkString(" & ") + ")"
  }
  object Conjunction {
    def apply(terms: Term*): Conjunction = new Conjunction(SortedSet(terms:_*))

    implicit def ordering: Ordering[Conjunction] = new Ordering[Conjunction] {
      def compare(x: Conjunction, y: Conjunction): Int = {
        (x.terms.size compareTo y.terms.size) match {
          case 0 => {
            // Equal number of terms
            x.terms.toSeq.sorted
              .zip(y.terms.toSeq.sorted)
              .map { { case (x, y) => Term.ordering.compare(x, y) } }
              .filter(_ != 0)
              .headOption.getOrElse(0)
          }

          case other => other
        }
      }
    }
  }

  case class Disjunction(conjuncts: Set[Conjunction]) {
    def |(other: Term) = Disjunction(conjuncts + Conjunction(other))
    def |(other: Conjunction) = Disjunction(conjuncts + other)
    def |(other: Disjunction) = Disjunction(conjuncts ++ other.conjuncts)
    def withoutUnsat = Disjunction(conjuncts.filter(c => c.terms.exists(t => c.terms.contains(!t))))
    override def toString() =
      if (conjuncts.isEmpty) "false"
      else conjuncts.mkString(" | ")
  }
  object Disjunction {
    def apply(conjuncts: Conjunction*) = new Disjunction(SortedSet(conjuncts:_*))
  }

  /**
    * Represents an implicant by storing the bits that are set and the bits that may differ. Note
    * that the set bits and differ bits must always be disjoint sets.
    * @param set The bits that must be true
    * @param differ The bits that may differ (introduced by combining other implicants)
    */
  case class Implicant(set: BitSet, differ: BitSet) {
    /**
      * Checks if this implicant is equal to the other implicant, or could be created by combining
      * the other implicant with another implicant.
      */
    def contains(other: Implicant) = {
      // The result of combining the other implicant with another would have a subset of the set
      // bits, a superset of the differ bits, and anything removed from the set bits must be in the
      // differ bits.
      // Since set and differ are disjoint, we can use the symmetric difference (XOR) of set bits
      // because if a bit is in `set`, it will not be in `differ`, and thus if `set` is not a
      // subset of `other.set`, the symmetric diff of the two will not be a subset of `differ`.
      (set ^ other.set).subsetOf(differ) && other.differ.subsetOf(differ)
    }

    /**
      * Checks if this implicant could be created by combining the given term with some other
      * term(s). Same thing as contains for an implicant, but we don't have to check
      * `other.differ`.
      */
    def contains(minterm: BitSet) =
      (set ^ minterm).subsetOf(differ)

  }

  /**
    * Reduces a collection of implicants by combining terms.
    * @param terms The number of bits that are considered.
    * @param implicants The collection of implicants that will be reduced.
    * @return The reduced collection if any terms can be combined, otherwise None.
    */
  def reduce(terms: Integer, implicants: Seq[Implicant]): Option[Seq[Implicant]] = {
    val reduced = mutable.ArrayBuffer[Implicant]()
    var changed = false

    // Only add an implicant if it is not contained by another implicant
    def add(imp: Implicant): Unit = {
      if (!changed || !reduced.exists(_.contains(imp)))
        reduced += imp
    }

    // Group the implicants 
    val grouped = implicants.groupBy(_.set.size)

    // Do one iteration for every possible number of set bits
    for (i <- 0 to terms) {
      // Iterate through all the terms with `i` set bits
      for (a <- grouped.getOrElse(i, Seq.empty)) {
        var combined = false

        // Iterate through all the terms with `i + 1` set bits
        for (b <- grouped.getOrElse(i + 1, Seq.empty)) {
          // A has one fewer bits set than B
          // Combine if A and B differ by 1 bit
          val diff = (a.set ^ b.set) | (a.differ ^ b.differ)
          if (diff.size == 1) {
            
            combined = true
            changed = true

            // Get the bit that differs
            val diffValue = diff.head
            if (b.set.contains(diffValue)) {
              // Since B has more set bits and A and B differ in their set values, the different
              // bit must be in B
              add(Implicant(a.set, a.differ + diffValue))
            } else {
              // Otherwise, A and B differ in the "differed" values by one bit, so use the larger
              // set (equivalent to the union since they differ by only one value).
              add(Implicant(a.set, a.differ | b.differ))
            }
          }
        }

        // If A cannot be combined with anything, add it
        if (!combined) add(a)
      }
    }

    if (changed) Some(reduced) else None
  }

  /**
    * Creates an array of term IDs for all terms used in the disjunction, so that the index in
    * this array can be used as a bit number, instead of using the term IDs which are not necessarily
    * sequential.
    */
  def compactIds(disjunction: Disjunction): Array[Integer] = {
    val allIds: Set[Integer] = disjunction.conjuncts.flatMap(c => c.terms.map(_.id))
    allIds.toSeq.sorted.toArray
  }

  /**
    * Finds all possible combinations of bits that make this disjunction evaluate to true. This
    * may be more than the number of conjuncts, since not all conjuncts may include all terms.
    * @param bitIds The mapping of bits to term IDs.
    */
  def computeMinterms(bitIds: Array[Integer], disjunction: Disjunction): Set[BitSet] = {
    disjunction.conjuncts.flatMap(c => {
      // Find all possible combinations of missing bits, and combine each combination with set bits
      // to find all possible combinations of set bits that make this conjunct true
      val bits = BitSet((0 until bitIds.length): _*)
      val setBits = bits.filter(bit => c.terms.exists(t => t.id == bitIds(bit) && t.value))

      // Check for a contradiction: a bit that is both true and false
      if (setBits.exists(bit => c.terms.contains(Term(bitIds(bit), false)))) {
        Set.empty
      } else {
        val missingBits = bits.filter(bit => !c.terms.exists(_.id == bitIds(bit)))
        missingBits.subsets().map(setBits | _)
      }
    })
  }

  /**
    * Converts an implicant to a conjunct of actual terms.
    */
  def toConjunct(bitIds: Array[Integer], imp: Implicant) =
    Conjunction(
      (0 until bitIds.length)
        .filter(bit => !imp.differ.contains(bit)) // remove bits that are not specified
        .map(bit => Term(bitIds(bit), imp.set.contains(bit))): _*)

  /**
    * Simplify a disjunction using the Quine-McClusky algorithm and Petrick's method.
    * NOTE: The behavior is undefined when given an unsatisfiable conjunction (i.e. a & !a).
    */
  def simplify(disjunction: Disjunction): Disjunction = {
    // Convert variable IDs to bits
    val bitIds = compactIds(disjunction)
    // Find all minterms
    val minTerms = computeMinterms(bitIds, disjunction)

    // Create an initial implicant set
    var implicants = minTerms.toSeq.map(Implicant(_, BitSet()))

    // Reduce the implicant set until it cannot be reduced
    var reduced: Option[Seq[Implicant]] = Some(implicants)
    while (reduced.isDefined) {
      reduced = reduce(bitIds.length, implicants)
      implicants = reduced.getOrElse(implicants)
    }

    // "Label" each reduced implicant by creating an array of them and using the array index as a
    // label.
    val implicantIndex = implicants.toArray

    // Create a list to contain resolved conjuncts
    val conjuncts = mutable.Set[Conjunction]()

    // Create an implicant table where each row represents a minterm, and each column in a row is 
    // the label of an implicant that the minterm implies.
    val implicantTable = minTerms.view
      .map(m => (m, (0 until implicantIndex.length).filter(i => implicantIndex(i).contains(m)).toSet))
      .toList

    // Find all the essential implicants
    val essential = implicantTable
      .collect { case (_, implicants) if implicants.size == 1 => implicants.head }
      .toSet

    // Add all essential implicants directly to the conjunct
    essential.foreach(i => conjuncts += toConjunct(bitIds, implicantIndex(i)))

    // Find the combinations of implicants required by min-terms that are not covered by the
    // essential prime implicants. For each combination, if any one of the implicants are included,
    // that minterm will be covered.
    // Then, create an expression that is true if *all* of these minterms are covered
    // (i.e. (1 | 2) & (2 | 3) & ...
    // Distribute that expression to find the SOP form that is true when all minterms are covered.
    // Picking any one of the resulting conjuncts will result in all of the minterms being covered.
    val petrick = implicantTable.view
      .collect {
        case (m, implicants) if !essential.exists(e => implicantIndex(e).contains(m)) =>
          implicants.diff(essential)
      }
      .foldLeft(Set[Set[Int]]())((sop, implicants) =>
        if (sop.isEmpty) implicants.map(Set(_))
        else multiplySOP(sop, implicants))

    // If not all implicants are essential prime implicants, compute the smallest expression
    // that will cover the rest
    if (!petrick.isEmpty) {
      // Find the size of the smallest conjunct in the SOP
      val minSize = petrick.map(_.size).min
      // Since there may be more than one conjunct of implicants with that size, find the one that
      // results in the fewest terms
      val minConjuncts = petrick
        .filter(s => s.size == minSize)
        .map(s => s.toList.map(i => toConjunct(bitIds, implicantIndex(i))))
        .minBy(_.map(_.terms.size).sum)

      // Add the conjuncts computed by Petrick's method to the conjuncts of essential prime
      // implicants
      conjuncts ++= minConjuncts
    }

    Disjunction(conjuncts.toSet)
  }

  /**
    * Multiplies a sum-of-products (SOP) expression by a new conjunct.
    * @param existing The base SOP expression, with terms represented as Ints.
    * @param conjunct The conjunct that will be AND'ed with the base.
    * @return A new SOP expression, created by distributing and simplifying.
    */
  def multiplySOP(base: Set[Set[Int]], conjunct: Set[Int]): Set[Set[Int]] = {
    val newSet = mutable.Set[Set[Int]]()
    for (x <- base)
    for (y <- conjunct)
      newSet += x + y
    
    // Note that the boolean identity XX = X is automatically handled through the use of Sets
    // Simplify with the identity XY + X = X
    newSet.retain(s => !newSet.exists(sub => sub.size < s.size && sub.subsetOf(s)))
    newSet.toSet
  }
}