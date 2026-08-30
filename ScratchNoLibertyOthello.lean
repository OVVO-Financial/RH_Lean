import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv

open RHLean.Proof

/-!
Kernel smoke test for the processed-seat no-liberty Othello seam.

This file checks that the whole no-liberty interface elaborates: every name
the closure argument depends on exists with the shape the seam expects.

It deliberately does not try to evaluate the two terminal cardinalities.  A
concrete probe would have to reduce `squareRootLowPrimeProcessedSeatCarrier`,
whose factorisation helpers are defined by well-founded recursion, and to
decide the `Finset.filter` predicates layered over it, which resolve through
the `Classical.propDecidable` local instance.  `Acc.rec` and `Classical.choice`
are both opaque to kernel reduction, so `#reduce` cannot return a numeral on
these terms; it gets stuck and prints the partially reduced term instead.
`#eval` is not an alternative either, since the definitions are noncomputable
for the same reason.  A numeric cross-check needs decidable, structurally
recursive definitions of the two sides, which is a separate piece of work.
-/

#check squareRootLowPrimeProcessedSeatNoLibertyMate
#check squareRootLowPrimeProcessedSeatNoLibertyMate_mem
#check squareRootLowPrimeProcessedSeatNoLibertyMate_involutive
#check squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg
#check finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
#check squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance
#check squareRootLowPrimeProcessedSeatNoLibertyBoundary
#check squareRootLowPrimeNoLibertyBoundaryWeight
#check SquareRootLowPrimeProcessedSeatDescendingFrontier
#check squareRootLowPrimeProcessedSeatNoLibertyStableEquivDescending
#check SquareRootLowPrimeDescendingBoundaryWeightEquiv
#check SquareRootLowPrimeNoLibertyWeightEquiv
#check squareRootLowPrimeNoLibertyWeightEquiv_sum_eq
#check squareRootLowPrimeNoLibertyWeightEquiv_boundaryMass_eq_runningImbalance
