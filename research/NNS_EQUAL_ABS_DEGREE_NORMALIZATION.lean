import Mathlib

/-!
# Equal-absolute-value degree normalization

For a finite real signed field whose nonzero cells all have one common
absolute magnitude, zero-target degree-one and degree-two normalized signed
ratios are exactly equal.

This is the algebraic currency converter needed before entering the reciprocal
owner-energy tree.  It is intentionally generic: no prime, Mobius, VF, or
first-bad structure appears here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- If a finite signed field has constant absolute magnitude on its carrier,
its degree-one normalized signed ratio equals its degree-two normalized signed
ratio.  The zero-mass and empty-carrier cases are included. -/
theorem zeroTargetNormalizedDegreeOne_eq_degreeTwo_of_eqAbs
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (c : ℝ)
    (habs : ∀ x ∈ s, |f x| = c) :
    (∑ x ∈ s, f x) / (∑ x ∈ s, |f x|) =
      (∑ x ∈ s, f x * |f x|) /
        (∑ x ∈ s, |f x| ^ 2) := by
  by_cases hs : s = ∅
  · simp [hs]
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
  by_cases hc : c = 0
  · have hfzero : ∀ x ∈ s, f x = 0 := by
      intro x hx
      apply abs_eq_zero.mp
      simpa [hc] using habs x hx
    have hsumF : (∑ x ∈ s, f x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hfzero x hx
    have hsumAbs : (∑ x ∈ s, |f x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hfzero x hx, abs_zero]
    have hsumSignedSq : (∑ x ∈ s, f x * |f x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hfzero x hx]
      norm_num
    have hsumSq : (∑ x ∈ s, |f x| ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hfzero x hx]
      norm_num
    rw [hsumF, hsumAbs, hsumSignedSq, hsumSq]
    norm_num
  · have hcardNat : s.card ≠ 0 := Finset.card_ne_zero.mpr hsne
    have hcard : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast hcardNat
    have hsumAbs :
        (∑ x ∈ s, |f x|) = (s.card : ℝ) * c := by
      calc
        (∑ x ∈ s, |f x|) = ∑ _x ∈ s, c := by
          apply Finset.sum_congr rfl
          intro x hx
          exact habs x hx
        _ = (s.card : ℝ) * c := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hsumSignedSq :
        (∑ x ∈ s, f x * |f x|) =
          c * (∑ x ∈ s, f x) := by
      calc
        (∑ x ∈ s, f x * |f x|) =
            ∑ x ∈ s, f x * c := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [habs x hx]
        _ = (∑ x ∈ s, f x) * c := by
              rw [← Finset.sum_mul]
        _ = c * (∑ x ∈ s, f x) := by ring
    have hsumSq :
        (∑ x ∈ s, |f x| ^ 2) =
          (s.card : ℝ) * c ^ 2 := by
      calc
        (∑ x ∈ s, |f x| ^ 2) =
            ∑ _x ∈ s, c ^ 2 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [habs x hx]
        _ = (s.card : ℝ) * c ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsumAbs, hsumSignedSq, hsumSq]
  field_simp [hc, hcard]
  ring

end RHLean.Analysis
