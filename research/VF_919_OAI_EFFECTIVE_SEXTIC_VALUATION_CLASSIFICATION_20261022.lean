import Mathlib

/-!
# Finite effective prime-ideal valuation classification modulo six

This is the exact unconditional finite-arithmetic core of the proposed
Stage-II sextic resonance classifier.

An effective ideal is represented by its FINITELY SUPPORTED prime-ideal
valuation vector (PrimeIdeal →₀ ℕ). The original Eisenstein ideal labels,
including the two distinct prime ideals of a split rational prime, are
not collapsed to a rational norm.

For valuations between 0 and 2, equality modulo six is equivalent to
equality of ALL valuations. In particular no nonzero exponent difference
can be divisible by six.

IMPORTANT: This lemma does NOT by itself prove that OpenAI's actual
GaussianSubset source atoms factor as sextic characters of these
effective ideal vectors, that all original columns have valuations <=2,
or that the *restricted actual row family* detects distinct characters.
Those are source-specific Hecke / CRT / weight-audit obligations.
-/

noncomputable section
open scoped Classical BigOperators

namespace RHLean.Analysis

/-- The bounded-valuation sixth-power criterion. A quotient of two
    such formal ideals has exponent divisible by 6 at every prime
    precisely when they are identical formal ideals. -/
theorem oai_effective_ideal_resonance_iff_eq
    {ι : Type*} [DecidableEq ι]
    (v w : ι →₀ ℕ)
    (hv : ∀ p, v p ≤ 2) (hw : ∀ p, w p ≤ 2) :
    (∀ p, (6 : ℤ) ∣ ((v p : ℤ) - (w p : ℤ))) ↔ v = w := by
  constructor
  · intro h
    ext p
    obtain ⟨k, hk⟩ := h p
    have hA := hv p
    have hB := hw p
    omega
  · intro h p
    rw [h]
    simp

/-- Distinct bounded effective-ideal vectors have a prime-ideal
    coordinate carrying a NONZERO sextic exponent difference. -/
theorem oai_distinct_effective_ideals_have_nontrivial_sextic_coordinate
    {ι : Type*} [DecidableEq ι]
    (v w : ι →₀ ℕ)
    (hv : ∀ p, v p ≤ 2) (hw : ∀ p, w p ≤ 2)
    (hne : v ≠ w) :
    ∃ p, ¬ (6 : ℤ) ∣ ((v p : ℤ) - (w p : ℤ)) := by
  by_contra h
  push_neg at h
  exact hne ((oai_effective_ideal_resonance_iff_eq v w hv hw).mp h)

/-- A source column may occur under several distinct labels while
    sharing the SAME effective ideal exponent vector. The fiber map
    is therefore NOT assumed injective on column labels. -/
theorem oai_effective_column_resonance_iff_fiber_eq
    {ι α : Type*} [DecidableEq ι]
    (effective : α → ι →₀ ℕ)
    (hbound : ∀ a p, effective a p ≤ 2)
    (a b : α) :
    (∀ p, (6 : ℤ) ∣
       ((effective a p : ℤ) - (effective b p : ℤ))) ↔
      effective a = effective b :=
  oai_effective_ideal_resonance_iff_eq
    (effective a) (effective b) (hbound a) (hbound b)

/-- Once equality of effective vectors is established, the
    *native* class-of map is exactly the intended resonant partition.
    This is independent of any root-of-unity value at a SINGLE row. -/
theorem oai_effective_fiber_class_eq_of_val_mod_six
    {ι α : Type*} [DecidableEq ι]
    (effective : α → ι →₀ ℕ)
    (hbound : ∀ a p, effective a p ≤ 2)
    (a b : α)
    (hphase : ∀ p, (6 : ℤ) ∣
      ((effective a p : ℤ) - (effective b p : ℤ))) :
    effective a = effective b :=
  (oai_effective_column_resonance_iff_fiber_eq effective
    hbound a b).mp hphase

end RHLean.Analysis

#print axioms RHLean.Analysis.oai_effective_ideal_resonance_iff_eq
#print axioms RHLean.Analysis.oai_distinct_effective_ideals_have_nontrivial_sextic_coordinate
#print axioms RHLean.Analysis.oai_effective_column_resonance_iff_fiber_eq
#print axioms RHLean.Analysis.oai_effective_fiber_class_eq_of_val_mod_six
