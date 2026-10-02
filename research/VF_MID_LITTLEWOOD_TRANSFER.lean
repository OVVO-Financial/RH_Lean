import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Littlewood oscillation transferred to the native VF-mid coordinate

This file keeps the direct VF program honest about the asymptotic geometry.

The classical Littlewood theorem is not currently available as an imported
Mathlib theorem in this repository, so it is represented by an explicit
premise rather than by an axiom or an unconditional declaration.

Likewise, the existing unconditional VF/Li bridge is only recorded at the
coarse O(sqrt x) scale.  To transfer the sharper Littlewood oscillation one
needs the genuinely smaller statement

  VF_mid(x) - Li(x)
    = o(sqrt(x) / log(x) * log(log(log x))).

The main theorem below proves that these two inputs imply the identical
two-sided Littlewood-scale oscillation for pi(x) - VF_mid(x).

No RH hypothesis is used and no statement identifies VF_mid with Li or with
the actual prime-counting staircase.
-/

noncomputable section

namespace RHLean.Analysis

/-- The classical Littlewood oscillation scale for the prime-counting error.
Only points where this quantity is positive are used by the transfer theorem. -/
def vfMidLittlewoodScale (x : ℝ) : ℝ :=
  Real.sqrt x / Real.log x * Real.log (Real.log (Real.log x))

/-- Classical Littlewood oscillation, stated in the same real-cutoff
coordinates as the repository's prime-minus-Li error.

This is deliberately an input proposition: the classical theorem has not been
formalized in the currently imported dependency graph. -/
def PrimeLiLittlewoodOscillationStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      c * vfMidLittlewoodScale x ≤ vfMidPrimeLiError x) ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      vfMidPrimeLiError x ≤ -(c * vfMidLittlewoodScale x))

/-- The sharpened midpoint-quadrature statement actually needed to move
Littlewood's theorem from Li coordinates into VF-mid coordinates. -/
def VFMidLiLittlewoodNegligibleStatement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |vfMidLiError x| ≤ ε * vfMidLittlewoodScale x

/-- The resulting two-sided Littlewood oscillation in the native VF-mid
coordinate. -/
def VFMidLittlewoodOscillationStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      c * vfMidLittlewoodScale x ≤ vfMidPrimeError x) ∧
    (∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      vfMidPrimeError x ≤ -(c * vfMidLittlewoodScale x))

/-- Positive excursions survive subtraction of a smaller VF-minus-Li
quadrature error. -/
theorem vfMidPrimeError_ge_half_of_primeLi_ge
    {c x : ℝ}
    (hc : 0 < c)
    (hscale : 0 < vfMidLittlewoodScale x)
    (hprime :
      c * vfMidLittlewoodScale x ≤ vfMidPrimeLiError x)
    (hquad :
      |vfMidLiError x| ≤
        (c / 2) * vfMidLittlewoodScale x) :
    (c / 2) * vfMidLittlewoodScale x ≤ vfMidPrimeError x := by
  have hquadUpper :
      vfMidLiError x ≤ (c / 2) * vfMidLittlewoodScale x :=
    (le_abs_self (vfMidLiError x)).trans hquad
  rw [vfMidPrimeLiError_eq_primeError_add_liError] at hprime
  nlinarith

/-- Negative excursions survive subtraction of a smaller VF-minus-Li
quadrature error. -/
theorem vfMidPrimeError_le_neg_half_of_primeLi_le
    {c x : ℝ}
    (hc : 0 < c)
    (hscale : 0 < vfMidLittlewoodScale x)
    (hprime :
      vfMidPrimeLiError x ≤ -(c * vfMidLittlewoodScale x))
    (hquad :
      |vfMidLiError x| ≤
        (c / 2) * vfMidLittlewoodScale x) :
    vfMidPrimeError x ≤
      -((c / 2) * vfMidLittlewoodScale x) := by
  have hquadLower :
      -((c / 2) * vfMidLittlewoodScale x) ≤ vfMidLiError x := by
    have hnegAbs : -|vfMidLiError x| ≤ vfMidLiError x :=
      neg_abs_le (vfMidLiError x)
    have hnegBound :
        -((c / 2) * vfMidLittlewoodScale x) ≤ -|vfMidLiError x| :=
      neg_le_neg hquad
    exact hnegBound.trans hnegAbs
  rw [vfMidPrimeLiError_eq_primeError_add_liError] at hprime
  nlinarith

/-- **Littlewood transfer into VF-mid coordinates.**

If the classical prime-minus-Li discrepancy has two-sided Littlewood-scale
excursions and the deterministic VF-minus-Li midpoint quadrature error is
little-o of that scale, then prime-minus-VF has the same two-sided scale.

The output constant is exactly one half of the input Littlewood constant. -/
theorem vfMidLittlewoodOscillation_of_primeLi_of_quadrature
    (hLittlewood : PrimeLiLittlewoodOscillationStatement)
    (hquad : VFMidLiLittlewoodNegligibleStatement) :
    VFMidLittlewoodOscillationStatement := by
  rcases hLittlewood with ⟨c, hc, hpos, hneg⟩
  have hhalf : 0 < c / 2 := by positivity
  rcases hquad (c / 2) hhalf with ⟨Xq, hXq⟩
  refine ⟨c / 2, hhalf, ?_, ?_⟩
  · intro X
    rcases hpos (max X Xq) with ⟨x, hx, hscale, hprime⟩
    have hxX : X ≤ x := (le_max_left X Xq).trans hx
    have hxq : Xq ≤ x := (le_max_right X Xq).trans hx
    refine ⟨x, hxX, hscale, ?_⟩
    exact vfMidPrimeError_ge_half_of_primeLi_ge
      hc hscale hprime (hXq x hxq)
  · intro X
    rcases hneg (max X Xq) with ⟨x, hx, hscale, hprime⟩
    have hxX : X ≤ x := (le_max_left X Xq).trans hx
    have hxq : Xq ≤ x := (le_max_right X Xq).trans hx
    refine ⟨x, hxX, hscale, ?_⟩
    exact vfMidPrimeError_le_neg_half_of_primeLi_le
      hc hscale hprime (hXq x hxq)

/-- The transfer can also be used one-sidedly: any positive Littlewood
excursion beyond the quadrature threshold yields a positive VF excursion of
half the same normalized size. -/
theorem exists_vfMid_positiveLittlewoodExcursion_above
    (hLittlewood : PrimeLiLittlewoodOscillationStatement)
    (hquad : VFMidLiLittlewoodNegligibleStatement)
    (X : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      c * vfMidLittlewoodScale x ≤ vfMidPrimeError x := by
  rcases vfMidLittlewoodOscillation_of_primeLi_of_quadrature
      hLittlewood hquad with
    ⟨c, hc, hpos, _hneg⟩
  rcases hpos X with ⟨x, hx, hs, he⟩
  exact ⟨c, hc, x, hx, hs, he⟩

/-- Symmetric one-sided negative form. -/
theorem exists_vfMid_negativeLittlewoodExcursion_above
    (hLittlewood : PrimeLiLittlewoodOscillationStatement)
    (hquad : VFMidLiLittlewoodNegligibleStatement)
    (X : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x : ℝ,
      X ≤ x ∧
      0 < vfMidLittlewoodScale x ∧
      vfMidPrimeError x ≤ -(c * vfMidLittlewoodScale x) := by
  rcases vfMidLittlewoodOscillation_of_primeLi_of_quadrature
      hLittlewood hquad with
    ⟨c, hc, _hpos, hneg⟩
  rcases hneg X with ⟨x, hx, hs, he⟩
  exact ⟨c, hc, x, hx, hs, he⟩

end RHLean.Analysis
