import Mathlib
import «research.SQUARE_SHELL_MASK_ENERGY_20261030»
import «research.SQUARE_SHELL_INCIDENCE_COMPENSATION_LEAN»

/-!
# Exact physical Euler / compensated-incidence synthesis

The inverse incidence below is evaluated on the actual Mobius divisor profile,
not an arbitrary supplied profile or a smooth expectation. Existing finite
Mobius inversion then identifies every divisor channel with the corrected
original historical Euler coefficient. All Gram cross terms are retained.

Its identification with the greatest-prime z-a interpretation is the
corresponding finite prime/cofactor reindexing, not a claimed analytic bound.
The h=1 residual is still present and still requires signed arithmetic.
-/
noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators
namespace RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Actual compensated residual, recovered from the genuine physical
square-shell Mobius incidence by finite upper-divisor inversion. -/
def synthesisCompensatedIncidence (R c : ℕ) : ℤ :=
  -shellIncidenceCompensator R (synthesisDivisorMobiusWindow R) c

/-- Every physical divisor channel matches the corrected original Euler
source; no independent-sign or continuation hypothesis is involved. -/
theorem synthesisCompensatedIncidence_profile
    (R h : ℕ) (hR : 3 ≤ R) (hh : 1 ≤ h) (hhR : h ≤ R) :
    shellDivisibilityProfile R (synthesisCompensatedIncidence R) h =
      synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h := by
  have hinv := shellIncidenceCompensator_matches R h
    (synthesisDivisorMobiusWindow R) hh hhR
  have hsum :
      shellDivisibilityProfile R (synthesisCompensatedIncidence R) h =
      -synthesisDivisorMobiusWindow R h := by
    unfold shellDivisibilityProfile synthesisCompensatedIncidence
    rw [← hinv, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hd : h ∣ c <;> simp [hd]
  rw [hsum, synthesisDivisorEuler_eq_neg_mobius_add_corner R h hR]
  ring

/-- The arbitrary SIGNED physical GCD/divisor kernel, with no positivity or
stationarity premise. Choosing the Mobius-inverted band weights yields the
original GCD-band form. -/
def synthesisDivisorGramKernel (R : ℕ) (weight : ℕ → ℤ) (c cp : ℕ) : ℤ :=
  ∑ h ∈ Finset.Icc 1 R, if h ∣ c ∧ h ∣ cp then weight h else 0

lemma synthesisDivisorGram_factor
    (R : ℕ) (weight u : ℕ → ℤ) :
    shellBilinear (Finset.Icc 1 R) (synthesisDivisorGramKernel R weight) u u =
      ∑ h ∈ Finset.Icc 1 R, weight h * (shellDivisibilityProfile R u h)^2 := by
  unfold shellBilinear synthesisDivisorGramKernel shellDivisibilityProfile
  simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro cp _hcp
  by_cases h1 : h ∣ c <;> by_cases h2 : h ∣ cp <;> simp [h1,h2] <;> ring

/-- This is the actual shared quadratic form. It includes squarefree and
squareful masks, arbitrary signed weights, and every cross-cofactor term. -/
theorem synthesisCompensatedIncidence_gram
    (R : ℕ) (weight : ℕ → ℤ) (hR : 3 ≤ R) :
    shellBilinear (Finset.Icc 1 R) (synthesisDivisorGramKernel R weight)
      (synthesisCompensatedIncidence R) (synthesisCompensatedIncidence R) =
    ∑ h ∈ Finset.Icc 1 R, weight h *
      (synthesisDivisorEulerWindow R h - synthesisDivisorCornerWindow R h)^2 := by
  rw [synthesisDivisorGram_factor]
  apply Finset.sum_congr rfl
  intro h hh
  rw [synthesisCompensatedIncidence_profile R h hR
    (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hh).2]

/-- The unit channel is not lost in the cross-coordinate transform. -/
theorem synthesisCompensatedIncidence_total
    (R : ℕ) (hR : 3 ≤ R) :
    (∑ c ∈ Finset.Icc 1 R, synthesisCompensatedIncidence R c) =
      -synthesisDivisorMobiusWindow R 1 := by
  have h := synthesisCompensatedIncidence_profile R 1 hR (by omega) (by omega)
  simp only [shellDivisibilityProfile, one_dvd, ite_true] at h
  rw [synthesisDivisorEuler_eq_neg_mobius_add_corner R 1 hR] at h
  linear_combination h

#print axioms synthesisCompensatedIncidence_profile
#print axioms synthesisDivisorGram_factor
#print axioms synthesisCompensatedIncidence_gram
#print axioms synthesisCompensatedIncidence_total
end RHLean.Proof
