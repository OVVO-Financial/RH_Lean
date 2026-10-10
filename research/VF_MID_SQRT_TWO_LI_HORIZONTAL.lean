import Mathlib
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import «research.VF_MID_ALIGNED_STEP_GRAPH»

/-!
# Direct Li-to-VF horizontal error bridge at original square endpoints

This is strictly more precise than invoking *only* PNT, because
VF_mid - Li_2 already has a proven *uniform O(1)* bound at square
endpoints in VF_MID_LI_UNIFORM_QUADRATURE.lean.

Two separate logical objects must be distinguished:
  1. Uniform O(1) deterministic quadrature error Li_2 - VF_mid:
     already proved, requiring no information about the primes.
  2. Actual arithmetic pi - Li_2 error: quantitative information
     strictly stronger than the bare PNT is required to bound it.

Pointwise "VF is always closer than Li" is NOT assumed or proved;
the exact squared-error comparison below determines the sign.
The vertical phase sqrt(2) is additive and therefore changes
these height errors by a bounded constant only.

The comparison retains *Nat.primeCounting* as the true pi.
-/

noncomputable section

namespace RHLean.Analysis

/-- Genuine prime minus the repo-normalized logarithmic integral
at the ORIGINAL integer square endpoint. -/
def vfMidSquarePrimeLi2Error (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ) -
    vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)

/-- Signed quadrature difference: positive when Li_2 exceeds the
real cumulative VF square-block mass. -/
def vfMidSquareLi2MinusVF (R : ℕ) : ℝ :=
  vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2) -
    vfMidFinishedMass R

/-- Exact decomposition of the ACTUAL prime discrepancy with VF
through the actual prime discrepancy with Li_2.
It cannot be replaced by either a PNT limit or a fantasy staircase. -/
theorem vfMidSquareActualPrimeVF_eq_primeLi2_add_quadrature
    (R : ℕ) :
    vfMidDirectSquareEndpointError R =
      vfMidSquarePrimeLi2Error R +
        vfMidSquareLi2MinusVF R := by
  unfold vfMidDirectSquareEndpointError vfMidSquarePrimeLi2Error
    vfMidSquareLi2MinusVF
  ring

/-- The deterministic Li_2-to-VF endpoint gap is already rigorously
uniformly bounded, by the compiled midpoint quadrature theorem. -/
theorem vfMidSquareLi2MinusVF_abs_le_uniform
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidSquareLi2MinusVF R| ≤
      vfMidLiSquareEndpointUniformConstant := by
  have hquad := abs_vfMidLiError_sq_le_uniform (R := R) hR
  unfold vfMidLiError at hquad
  rw [vfMid_sq hR] at hquad
  unfold vfMidSquareLi2MinusVF
  simpa only [abs_sub_comm] using hquad

/-- Any proved pi-Li_2 error bound transfers DIRECTLY to the
original actual pi-VF error with only a FIXED uniform additive cost. -/
theorem vfMidSquareActualPrimeVF_abs_le_primeLi2_abs_add_uniform
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidDirectSquareEndpointError R| ≤
      |vfMidSquarePrimeLi2Error R| +
        vfMidLiSquareEndpointUniformConstant := by
  rw [vfMidSquareActualPrimeVF_eq_primeLi2_add_quadrature]
  exact (abs_add_le _ _).trans
    (add_le_add_left (vfMidSquareLi2MinusVF_abs_le_uniform R hR) _)

/-- Conversely an original VF arithmetic bound transfers to Li_2
with exactly the same uniform deterministic quadrature cost. -/
theorem vfMidSquareActualPrimeLi2_abs_le_primeVF_abs_add_uniform
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidSquarePrimeLi2Error R| ≤
      |vfMidDirectSquareEndpointError R| +
        vfMidLiSquareEndpointUniformConstant := by
  have heq := vfMidSquareActualPrimeVF_eq_primeLi2_add_quadrature R
  have hgap := vfMidSquareLi2MinusVF_abs_le_uniform R hR
  have htri :
      |vfMidDirectSquareEndpointError R -
          vfMidSquareLi2MinusVF R| ≤
        |vfMidDirectSquareEndpointError R| +
          |vfMidSquareLi2MinusVF R| :=
    abs_sub_le _ _
  rw [heq] at htri
  have hcancel :
      vfMidSquarePrimeLi2Error R +
          vfMidSquareLi2MinusVF R -
            vfMidSquareLi2MinusVF R =
        vfMidSquarePrimeLi2Error R := by ring
  rw [hcancel] at htri
  linarith

/-- The exact distance comparison shows why observing VF closer in
a finite numerical sample does NOT prove a universal sign theorem.

When L=Li_2 and F=original VF, the squared absolute-error
advantage of Li over VF is
  (pi-F)^2 - (pi-L)^2 = (L-F)*(2*pi-F-L).
It depends on ACTUAL pi and is not fixed by midpoint quadrature. -/
theorem vfMidSquareVF_vs_Li2_squaredErrors
    (R : ℕ) :
    (vfMidDirectSquareEndpointError R) ^ 2 -
        (vfMidSquarePrimeLi2Error R) ^ 2 =
      vfMidSquareLi2MinusVF R *
        (2 * (Nat.primeCounting (R ^ 2) : ℝ) -
          vfMidFinishedMass R -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)) := by
  unfold vfMidDirectSquareEndpointError vfMidSquarePrimeLi2Error
    vfMidSquareLi2MinusVF
  ring

/-- A quantitative bound for Li_2 now delivers a quantitative bound
for genuine pi minus VF. This is a finite theorem, no RH claim. -/
theorem vfMidSquareActualPrimeVF_abs_le_of_Li2_error
    (R : ℕ) (hR : 2 ≤ R) (E : ℝ)
    (hLi : |vfMidSquarePrimeLi2Error R| ≤ E) :
    |vfMidDirectSquareEndpointError R| ≤
      E + vfMidLiSquareEndpointUniformConstant := by
  exact (vfMidSquareActualPrimeVF_abs_le_primeLi2_abs_add_uniform
    R hR).trans (add_le_add_right hLi _)

/-- sqrt(2) chosen vertical *real* phase contributes only its
bounded fixed constant to any direct Li_2 or VF discrepancy.
This is independent of how accurately actual primes follow Li_2. -/
theorem vfMidSquareSqrtTwoPhase_primeVF_error_eq
    (R : ℕ) :
    vfMidAlignedSquareEndpointError (Real.sqrt 2) R =
      vfMidDirectSquareEndpointError R - Real.sqrt 2 := by
  exact vfMidAlignedSquareEndpointError_eq_direct_sub (Real.sqrt 2) R

end RHLean.Analysis
