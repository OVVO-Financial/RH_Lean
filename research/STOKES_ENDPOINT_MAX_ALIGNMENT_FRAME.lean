import Mathlib
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT»

/-!
# Root-scale frame majorant from completed prime periods

The preceding file proves the deterministic pairwise fact: after deleting every
completed cross period, the endpoint correlation between distinct period-`p`
and period-`q` characters has norm at most `p*q`.  With reciprocal weights this
makes every off-diagonal prime pair cost at most one.

This file sums that fact without invoking probability, PNT, or an asymptotic
spacing model.  If a finite prime set `S` has reciprocal-square budget at most
`1/4`, then its full reciprocal endpoint Gram majorant is bounded by

  N/4 + |S|^2.

Consequently for `N <= R^2` and `|S| <= R` the majorant is at most
`(5/4) R^2`.

This is a frame majorant only.  The separate physical bridge from the final
signed Stokes boundary is not asserted in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- Off-diagonal reciprocal prime-period alignment majorant at endpoint length
`N`.  The diagonal is deliberately excluded by `S.erase p`. -/
def primePeriodReciprocalOffDiagonalMajorant
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S,
    ∑ q ∈ S.erase p,
      ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
        ‖primeWheelDirichletKernel W N
          (primePeriodFrequency W p - primePeriodFrequency W q)‖

/-- Diagonal reciprocal mass for `N` physical samples. -/
def primePeriodReciprocalDiagonalMajorant
    (N : ℕ) (S : Finset ℕ) : ℝ :=
  (N : ℝ) * ∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2

/-- Complete elementary frame majorant. -/
def primePeriodReciprocalFrameMajorant
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ) : ℝ :=
  primePeriodReciprocalDiagonalMajorant N S +
    primePeriodReciprocalOffDiagonalMajorant W N S

/-- Every distinct reciprocal prime-period pair costs at most one, hence all
off-diagonal alignment is bounded by the square of the number of modes. -/
theorem primePeriodReciprocalOffDiagonalMajorant_le_card_sq
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hmod : ∀ p ∈ S, p ∣ W.modulus) :
    primePeriodReciprocalOffDiagonalMajorant W N S ≤
      (S.card : ℝ) ^ 2 := by
  unfold primePeriodReciprocalOffDiagonalMajorant
  calc
    (∑ p ∈ S,
        ∑ q ∈ S.erase p,
          ((1 : ℝ) / (p : ℝ)) * ((1 : ℝ) / (q : ℝ)) *
            ‖primeWheelDirichletKernel W N
              (primePeriodFrequency W p - primePeriodFrequency W q)‖) ≤
      ∑ p ∈ S, ∑ q ∈ S.erase p, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        have hqData := Finset.mem_erase.mp hq
        have hqS : q ∈ S := hqData.2
        have hpq : p ≠ q := by
          exact Ne.symm hqData.1
        exact
          invPrime_mul_invPrime_mul_norm_primePeriodDifferenceDirichlet_le_one
            W N (hprime p hp) (hprime q hqS) hpq
              (hmod p hp) (hmod q hqS)
    _ = ∑ p ∈ S, ((S.erase p).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp
    _ ≤ ∑ _p ∈ S, (S.card : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact_mod_cast Finset.card_le_card (Finset.erase_subset p S)
    _ = (S.card : ℝ) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

/-- A quarter reciprocal-square budget gives the diagonal-plus-off-diagonal
frame majorant `N/4 + |S|^2`. -/
theorem primePeriodReciprocalFrameMajorant_le_quarter_length_add_card_sq
    (W : PrimeWheelFiniteSystem) (N : ℕ) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hmod : ∀ p ∈ S, p ∣ W.modulus)
    (hbudget :
      (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2) ≤ 1 / 4) :
    primePeriodReciprocalFrameMajorant W N S ≤
      (1 / 4 : ℝ) * (N : ℝ) + (S.card : ℝ) ^ 2 := by
  have hoff :=
    primePeriodReciprocalOffDiagonalMajorant_le_card_sq
      W N S hprime hmod
  have hdiag :
      primePeriodReciprocalDiagonalMajorant N S ≤
        (1 / 4 : ℝ) * (N : ℝ) := by
    unfold primePeriodReciprocalDiagonalMajorant
    have hN : 0 ≤ (N : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hbudget hN
    nlinarith
  unfold primePeriodReciprocalFrameMajorant
  linarith

/-- **Root-scale maximum-alignment theorem.**

If the endpoint clock has length at most `R^2`, there are at most `R` active
prime periods, and their reciprocal-square mass is at most `1/4`, then the
complete deterministic prime-period alignment majorant is at most
`(5/4) R^2`. -/
theorem primePeriodReciprocalFrameMajorant_le_five_fourths_root_sq
    (W : PrimeWheelFiniteSystem) (N R : ℕ) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hmod : ∀ p ∈ S, p ∣ W.modulus)
    (hbudget :
      (∑ p ∈ S, ((1 : ℝ) / (p : ℝ)) ^ 2) ≤ 1 / 4)
    (hN : N ≤ R ^ 2)
    (hcard : S.card ≤ R) :
    primePeriodReciprocalFrameMajorant W N S ≤
      (5 / 4 : ℝ) * (R : ℝ) ^ 2 := by
  have hframe :=
    primePeriodReciprocalFrameMajorant_le_quarter_length_add_card_sq
      W N S hprime hmod hbudget
  have hNreal : (N : ℝ) ≤ (R : ℝ) ^ 2 := by
    exact_mod_cast hN
  have hcardReal : (S.card : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hcard
  have hcard0 : 0 ≤ (S.card : ℝ) := by positivity
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  have hcardSq : (S.card : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    nlinarith
  nlinarith

end RHLean.Analysis
