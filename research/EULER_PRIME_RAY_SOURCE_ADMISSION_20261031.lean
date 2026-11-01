import Mathlib
import RHLean.Arithmetic.MoebiusDoubling
import «research.EULER_FRACTIONAL_COUPLED_20261027»

/-!
# Near-root prime-ray source admission

This module formalizes the occurrence-level carrier used by the accepted
near-root prime-ray telescope (claims `20261031-coordinator-2` and
`20261031-referee-7`).

For an odd cofactor `m` in the completed `v₂(a)=1` ray and a near-root
prime `q`, the row `(2m,q)` consists of two distinct positive indices
strictly below `R`. Its literal original Euler coefficient is exactly
`μ(m)`.

This is a source-admission and sign theorem only. It proves no summatory
Möbius identity, moment estimate, complete-source bound, endpoint gain, or RH.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius

namespace RHLean.Proof

/-- Every accepted near-root prime-ray row is a genuine original Euler row,
with its exact Möbius coefficient. -/
theorem eulerPrimeRay_row_admitted_and_weight
    (R q m : ℕ)
    (hR : 8 ≤ R)
    (hq : Nat.Prime q)
    (hqLow : R / 2 < q)
    (hqHigh : q < R)
    (hmPos : 1 ≤ m)
    (hmHigh : m ≤ (R - 1) / 2)
    (hmOdd : Odd m) :
    0 < 2 * m ∧
      2 * m < R ∧
      0 < q ∧
      q < R ∧
      2 * m ≠ q ∧
      m < q ∧
      eulerMuQ (2 * m) * eulerMuQ q = eulerMuQ m := by
  have hqPos : 0 < q := hq.pos
  have hqNeTwo : q ≠ 2 := by omega
  have hqOdd : Odd q := hq.odd_of_ne_two hqNeTwo
  obtain ⟨t, ht⟩ := hqOdd
  have hDistinct : 2 * m ≠ q := by
    intro h
    omega
  have hMuTwo : μ (2 * m) = -μ m :=
    RHLean.Arithmetic.moebius_two_mul_of_odd m hmOdd
  have hMuQ : μ q = -1 :=
    ArithmeticFunction.moebius_apply_prime hq
  refine ⟨by omega, by omega, hqPos, hqHigh, hDistinct, by omega, ?_⟩
  simp [eulerMuQ, hMuTwo, hMuQ]

#print axioms eulerPrimeRay_row_admitted_and_weight

end RHLean.Proof
