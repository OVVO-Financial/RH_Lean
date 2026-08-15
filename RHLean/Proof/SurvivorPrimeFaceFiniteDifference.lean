import Mathlib
import RHLean.Arithmetic.BooleanCubeFiniteDifference
import RHLean.Proof.SurvivorPrimeFaceRealization

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Arithmetic

/-!
# Actual survivor fibres as finite Boolean derivatives

The prime-face realization identifies the actual fixed-`q` survivor cofactor
mass with an alternating Boolean-supported sum.  The generic two-pivot finite
difference theorem therefore applies directly to the real survivor selector,
without decomposing its V-shaped support into monotone pieces.
-/

/-- Any two distinct prime-face coordinates below `q` put the actual fixed-`q`
survivor mass on an exact four-point Boolean stencil. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_twoPivotDifference
    (Λ : ℝ) (t : ℕ) {q a b : ℕ}
    (hq : q.Prime)
    (ha : a ∈ survivorPrimeFaceAmbient q)
    (hb : b ∈ survivorPrimeFaceAmbient q)
    (hab : a ≠ b) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          (((survivorPrimeFaceAmbient q).erase a).erase b).powerset,
          booleanCubeSign u *
            booleanTwoPivotDifference a b
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  rw [survivorFixedPrimeCofactorMass_eq_neg_faceAlternating Λ t hq]
  rw [truncatedCubeAlternatingSum_eq_twoPivotDifference
    (survivorPrimeFaceHigh Λ t q) ha hb hab]

/-- For every prime `q >= 7`, primes `3` and `5` give a universal exact
four-point survivor stencil.  No residue or monotonicity hypothesis is needed. -/
theorem survivorFixedPrimeCofactorMass_eq_neg_three_five_difference
    (Λ : ℝ) (t : ℕ) {q : ℕ}
    (hqPrime : q.Prime) (hq : 7 ≤ q) :
    survivorFixedPrimeCofactorMass Λ t q =
      -(((∑ u ∈
          (((survivorPrimeFaceAmbient q).erase 3).erase 5).powerset,
          booleanCubeSign u *
            booleanTwoPivotDifference 3 5
              (survivorPrimeFaceHigh Λ t q) u : ℤ)) : ℂ) := by
  apply survivorFixedPrimeCofactorMass_eq_neg_twoPivotDifference Λ t hqPrime
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · unfold survivorPrimeFaceAmbient
    exact mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  · norm_num

/-- The four-point Boolean stencil has universal integer magnitude at most two. -/
theorem abs_booleanTwoPivotDifference_le_two
    {α : Type*} [DecidableEq α]
    (a b : α) (P : Finset α → Prop) (u : Finset α) :
    |booleanTwoPivotDifference a b P u| ≤ 2 := by
  unfold booleanTwoPivotDifference booleanPredicateIndicator
  by_cases h0 : P u <;>
    by_cases ha : P (insert a u) <;>
    by_cases hb : P (insert b u) <;>
    by_cases hab : P (insert a (insert b u)) <;>
    simp [h0, ha, hb, hab]

end RHLean.Proof
