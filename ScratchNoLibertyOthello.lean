import RHLean.Proof.SquareRootLowPrimeOppositeFixedClassification

open RHLean.Proof

private def terminal (R : Nat) := squareRootBornPostTailLowPrimeCutoff R

#eval (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
  10 1 0 (terminal 10)).card
#eval (squareRootLowPrimeProcessedSeatNoLibertyBoundary
  10 1 0 (terminal 10)).card
#eval squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
  10 1 0 (terminal 10)
#eval squareRootLowPrimeProcessedSeatNoLibertyBoundary
  10 1 0 (terminal 10)

#eval (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
  20 1 0 (terminal 20)).card
#eval (squareRootLowPrimeProcessedSeatNoLibertyBoundary
  20 1 0 (terminal 20)).card

#eval (squareRootLowPrimeProcessedSeatDescendingTerminalFrontier
  30 1 0 (terminal 30)).card
#eval (squareRootLowPrimeProcessedSeatNoLibertyBoundary
  30 1 0 (terminal 30)).card
