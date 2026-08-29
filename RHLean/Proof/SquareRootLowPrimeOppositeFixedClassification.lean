import Mathlib
import RHLean.Proof.CreationResponseOthelloInvolution
import RHLean.Proof.SquareRootLowPrimeCanonicalToggleRootCharge
import RHLean.Proof.SquareRootLowPrimeCanonicalLiberty
import RHLean.Proof.SquareRootLowPrimeGoGlobalPartner
import RHLean.Proof.SquareRootLowPrimeNoTogglePopulationBound

/-!
# Opposite-fixed endpoint classification

This module is the current kernel-checking surface for the two-direction
square-root Othello closure.  The substantive declarations below are added only
when they are proved from the actual terminal carriers; no arbitrary remainder
is introduced here.
-/

noncomputable section

namespace RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Sanity check that the canonical toggle carrier and the actual canonical
terminal carrier coexist in one current import graph. -/
theorem squareRootLowPrimeOppositeFixed_import_sanity
    (R K j U : ℕ) :
    squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U =
      squareRootLowPrimeProcessedSeatCanonicalTerminalFrontier R K j U := by
  rfl

end RHLean.Proof
