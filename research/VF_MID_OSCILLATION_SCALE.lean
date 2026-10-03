import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Native VF-mid oscillation scale transfer

This module deliberately avoids depending on any named classical oscillation
theorem.  It isolates only the asymptotic scale

  sqrt(x) / log(x) * log(log(log x)),

and proves the exact transfer principle needed by the direct VF program:

* if prime-minus-Li has arbitrarily large positive and negative excursions at
  that scale; and
* if the deterministic VF-minus-Li quadrature error is little-o of that scale,

then prime-minus-VF has arbitrarily large positive and negative excursions at
the same scale.

The arithmetic input and the deterministic quadrature input remain explicit.
No RH hypothesis is used.
-/

noncomputable section

namespace RHLean.Analysis

/-- Base square-root-over-log scale, comparable to one VF square-block mass. -/
def vfMidBlockScale (x : ℝ) : ℝ :=
  Real.sqrt x / Real.log x

/-- The asymptotic oscillation scale used by the direct VF analysis. -/
def vfMidOscillationScale (x : ℝ) : ℝ :=
  vfMidBlockScale x * Real.log (Real.log (Real.log x))

/-- The exact factor separating the oscillation scale from the one-block
square-root-over-log scale. -/
theorem vfMidOscillationScale_eq_blockScale_mul_tripleLog (x : ℝ) :
    vfMidOscillationScale x =
      vfMidBlockScale x * Real.log (Real.log (Real.log x)) := by
  rfl

/-- Two-sided actual prime-minus-Li excursions at the native oscillation scale.
This proposition is deliberately scale-based and does not name or assume any
particular source theorem. -/
def PrimeLiOscillationScaleStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      c * vfMidOscillationScale x ≤ vfMidPrimeLiError x) ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      vfMidPrimeLiError x ≤ -(c * vfMidOscillationScale x))

/-- The deterministic VF-minus-Li midpoint quadrature error is negligible
relative to the chosen oscillation scale. -/
def VFMidLiOscillationScaleNegligibleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |vfMidLiError x| ≤ ε * vfMidOscillationScale x

/-- Two-sided prime-minus-VF excursions at the same oscillation scale. -/
def VFMidOscillationScaleStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      c * vfMidOscillationScale x ≤ vfMidPrimeError x) ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      vfMidPrimeError x ≤ -(c * vfMidOscillationScale x))

/-- Positive scale excursions survive subtraction of a deterministic error
which is at most half the excursion amplitude. -/
theorem vfMidPrimeError_ge_half_of_primeLi_ge
    {c x : ℝ}
    (hprime :
      c * vfMidOscillationScale x ≤ vfMidPrimeLiError x)
    (hquad :
      |vfMidLiError x| ≤
        (c / 2) * vfMidOscillationScale x) :
    (c / 2) * vfMidOscillationScale x ≤ vfMidPrimeError x := by
  have hquadUpper :
      vfMidLiError x ≤ (c / 2) * vfMidOscillationScale x :=
    (le_abs_self (vfMidLiError x)).trans hquad
  rw [vfMidPrimeLiError_eq_primeError_add_liError] at hprime
  nlinarith

/-- Negative scale excursions survive subtraction of a deterministic error
which is at most half the excursion amplitude. -/
theorem vfMidPrimeError_le_neg_half_of_primeLi_le
    {c x : ℝ}
    (hprime :
      vfMidPrimeLiError x ≤ -(c * vfMidOscillationScale x))
    (hquad :
      |vfMidLiError x| ≤
        (c / 2) * vfMidOscillationScale x) :
    vfMidPrimeError x ≤
      -((c / 2) * vfMidOscillationScale x) := by
  have hquadLower :
      -((c / 2) * vfMidOscillationScale x) ≤ vfMidLiError x := by
    have hnegAbs : -|vfMidLiError x| ≤ vfMidLiError x :=
      neg_abs_le (vfMidLiError x)
    have hnegBound :
        -((c / 2) * vfMidOscillationScale x) ≤ -|vfMidLiError x| :=
      neg_le_neg hquad
    exact hnegBound.trans hnegAbs
  rw [vfMidPrimeLiError_eq_primeError_add_liError] at hprime
  nlinarith

/-- **Native oscillation-scale transfer.**

Any two-sided prime-minus-Li oscillation theorem at the chosen scale transfers
to prime-minus-VF once the deterministic midpoint quadrature error is little-o
of that same scale.

The output excursion constant is exactly one half of the input constant. -/
theorem vfMidOscillationScale_of_primeLi_of_quadrature
    (hosc : PrimeLiOscillationScaleStatement)
    (hquad : VFMidLiOscillationScaleNegligibleStatement) :
    VFMidOscillationScaleStatement := by
  rcases hosc with ⟨c, hc, hpos, hneg⟩
  have hhalf : 0 < c / 2 := by positivity
  rcases hquad (c / 2) hhalf with ⟨Xq, hXq⟩
  refine ⟨c / 2, hhalf, ?_, ?_⟩
  · intro X
    rcases hpos (max X Xq) with ⟨x, hx, hscale, hprime⟩
    have hxX : X ≤ x := (le_max_left X Xq).trans hx
    have hxq : Xq ≤ x := (le_max_right X Xq).trans hx
    refine ⟨x, hxX, hscale, ?_⟩
    exact vfMidPrimeError_ge_half_of_primeLi_ge
      hprime (hXq x hxq)
  · intro X
    rcases hneg (max X Xq) with ⟨x, hx, hscale, hprime⟩
    have hxX : X ≤ x := (le_max_left X Xq).trans hx
    have hxq : Xq ≤ x := (le_max_right X Xq).trans hx
    refine ⟨x, hxX, hscale, ?_⟩
    exact vfMidPrimeError_le_neg_half_of_primeLi_le
      hprime (hXq x hxq)

/-- Positive one-sided extraction from the scale-transfer theorem. -/
theorem exists_vfMid_positiveOscillationScaleExcursion_above
    (hosc : PrimeLiOscillationScaleStatement)
    (hquad : VFMidLiOscillationScaleNegligibleStatement)
    (X : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      c * vfMidOscillationScale x ≤ vfMidPrimeError x := by
  rcases vfMidOscillationScale_of_primeLi_of_quadrature
      hosc hquad with
    ⟨c, hc, hpos, _hneg⟩
  rcases hpos X with ⟨x, hx, hs, he⟩
  exact ⟨c, hc, x, hx, hs, he⟩

/-- Negative one-sided extraction from the scale-transfer theorem. -/
theorem exists_vfMid_negativeOscillationScaleExcursion_above
    (hosc : PrimeLiOscillationScaleStatement)
    (hquad : VFMidLiOscillationScaleNegligibleStatement)
    (X : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidOscillationScale x ∧
      vfMidPrimeError x ≤ -(c * vfMidOscillationScale x) := by
  rcases vfMidOscillationScale_of_primeLi_of_quadrature
      hosc hquad with
    ⟨c, hc, _hpos, hneg⟩
  rcases hneg X with ⟨x, hx, hs, he⟩
  exact ⟨c, hc, x, hx, hs, he⟩

end RHLean.Analysis
