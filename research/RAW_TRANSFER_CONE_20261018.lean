import Mathlib

/-!
# Raw native/Mobius transfer cone

This module formalizes the exact algebraic core of independently accepted claims
`20261018-owner-1` and `20261018-referee-6`.

On the genuine odd high-prime composite shell, let `A`, `B`, and `Z` be
the nonnegative native weights carried respectively by cofactors with Mobius
value `1`, `-1`, and `0`. The native mass is `A + B + Z`, while the
corresponding signed Mobius mass is `B - A`. Their squared gap factors as a
nonnegative transfer cone.

This is a raw-carrier scalar obstruction only. It does not identify the masked
original #915 returned-cell carrier, preserve its historical norm, or prove any
quantitative cancellation estimate.
-/

namespace RHLean.Analysis

/-- The squared native/Mobius mass gap factors into the two parity-sector
margins. This is the exact transfer-cone identity. -/
theorem rawTransferCone_sq_sub_sq (A B Z : ℝ) :
    (A + B + Z) ^ 2 - (B - A) ^ 2 = (2 * A + Z) * (2 * B + Z) := by
  ring

/-- Nonnegative parity-sector weights force the native mass square to dominate
the signed Mobius mass square. -/
theorem rawTransferCone_sq_nonneg
    (A B Z : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z) :
    0 ≤ (A + B + Z) ^ 2 - (B - A) ^ 2 := by
  rw [rawTransferCone_sq_sub_sq]
  exact mul_nonneg (by positivity) (by positivity)

/-- Equivalent order form of the raw transfer-cone obstruction. -/
theorem rawTransferCone_moebius_sq_le_native_sq
    (A B Z : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z) :
    (B - A) ^ 2 ≤ (A + B + Z) ^ 2 := by
  nlinarith [rawTransferCone_sq_nonneg A B Z hA hB hZ]

end RHLean.Analysis

#print axioms RHLean.Analysis.rawTransferCone_sq_sub_sq
#print axioms RHLean.Analysis.rawTransferCone_sq_nonneg
#print axioms RHLean.Analysis.rawTransferCone_moebius_sq_le_native_sq
