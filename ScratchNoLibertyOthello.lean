import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification

open RHLean.Proof

/-!
Kernel-only smoke test for the processed-seat no-liberty Othello seam.

The carriers in this proof path are deliberately noncomputable, so this file
must not use `#eval`.  The custom workflow checks the declarations themselves;
the final arithmetic stable-boundary theorem belongs in the imported module.
-/

#check squareRootLowPrimeProcessedSeatNoLibertyMate
#check squareRootLowPrimeProcessedSeatNoLibertyMate_mem
#check squareRootLowPrimeProcessedSeatNoLibertyMate_involutive
#check squareRootLowPrimeProcessedSeatNoLibertyMate_weight_neg
#check finiteOthelloStablePart_processedSeatNoLibertyMate_eq_descendingFrontier
#check squareRootLowPrimeProcessedSeatNoLibertyMate_stableMass_eq_runningImbalance
#check squareRootLowPrimeProcessedSeatNoLibertyBoundary
#check squareRootLowPrimeNoLibertyBoundaryWeight
