import RHLean.Proof.SquareRootLowPrimeNoLibertyFiniteEquiv

open RHLean.Proof

/-!
Kernel smoke test for the processed-seat no-liberty Othello seam.

The two tiny `#reduce` probes below deliberately use kernel reduction rather
than code generation.  They are a guard against attempting to prove an
incorrect finite equivalence: before constructing the general classifier we
compare the literal descending-frontier and tagged-boundary cardinalities on a
small terminal instance.
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

#reduce
  (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
    6 1 0 (squareRootBornPostTailLowPrimeCutoff 6)).card
#reduce
  (squareRootLowPrimeProcessedSeatNoLibertyBoundary
    6 1 0 (squareRootBornPostTailLowPrimeCutoff 6)).card
