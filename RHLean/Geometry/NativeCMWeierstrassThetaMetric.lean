import RHLean.Geometry.NativeCMWeierstrassThetaFrame

/-!
# The actual sigma metric and its exact period invariance

The metric is derived from the Hermitian form in the proved canonical-sigma
automorphy law. Its multiplier norm, lattice invariance and all-place
tangent length are exact. No class-group mean is assigned to a norm field.
The origin-chart comparison in ThetaFrame connects the same sigma section
to the literal origin section; completing the global analytic atlas and
its curvature identification remains separate from these calculations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Complex PeriodPair NumberField
open scoped ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open Weierstrass PeriodMean

variable (L : PeriodPair)

def multiplier (w z : ℂ) : ℂ :=
  sigmaSign L w * exp (π * latticeForm L z w + π / 2 * latticeForm L w w)

theorem multiplier_ne_zero (w z : ℂ) : multiplier L w z ≠ 0 :=
  mul_ne_zero (sigmaSign_ne_zero L w) (exp_ne_zero _)

theorem canonicalSigma_automorphy {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    canonicalSigma L (z + w) = multiplier L w z * canonicalSigma L z := by
  simpa only [multiplier, div_mul_eq_mul_div] using! canonicalSigma_add L hw z

theorem norm_multiplier_sq (w z : ℂ) :
    ‖multiplier L w z‖ ^ 2 =
      Real.exp (2 * π * (latticeForm L z w).re + π * (latticeForm L w w).re) := by
  rw [multiplier, norm_mul, norm_sigmaSign, one_mul, norm_exp, pow_two,
    ← Real.exp_add]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, zero_div, zero_mul, sub_zero]
  ring

theorem latticeForm_add_self_re (z w : ℂ) :
    (latticeForm L (z + w) (z + w)).re =
      (latticeForm L z z).re + 2 * (latticeForm L z w).re + (latticeForm L w w).re := by
  rw [latticeForm_add_left, latticeForm_add_right, latticeForm_add_right,
    ← conj_latticeForm L z w]
  simp only [Complex.add_re, conj_re]
  ring

/-- The squared norm in the canonical frame on the universal cover. -/
def fiberNormSq (z v : ℂ) : ℝ :=
  ‖v‖ ^ 2 * Real.exp (-π * (latticeForm L z z).re)

theorem fiberNormSq_pos {z v : ℂ} (hv : v ≠ 0) : 0 < fiberNormSq L z v :=
  mul_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)) (Real.exp_pos _)

/-- The actual multiplier is an isometry of these fibers. -/
theorem fiberNormSq_multiplier (w z v : ℂ) :
    fiberNormSq L (z + w) (multiplier L w z * v) = fiberNormSq L z v := by
  rw [fiberNormSq, fiberNormSq, norm_mul, mul_pow, norm_multiplier_sq,
    latticeForm_add_self_re]
  calc
    _ = ‖v‖ ^ 2 *
        (Real.exp (2 * π * (latticeForm L z w).re + π * (latticeForm L w w).re) *
        Real.exp (-π * ((latticeForm L z z).re + 2 * (latticeForm L z w).re +
          (latticeForm L w w).re))) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2 <;> ring

def sigmaNormSq (z : ℂ) : ℝ := fiberNormSq L z (canonicalSigma L z)

theorem sigmaNormSq_periodic {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    sigmaNormSq L (z + w) = sigmaNormSq L z := by
  rw [sigmaNormSq, canonicalSigma_automorphy L hw, fiberNormSq_multiplier]
  rfl

theorem sigmaNormSq_pos {z : ℂ} (hz : z ∉ L.lattice) : 0 < sigmaNormSq L z :=
  fiberNormSq_pos L ((canonicalSigma_eq_zero_iff L).not.mpr hz)

section PlaceComparison

open AllPlaceTangentPeriod

variable {F : Type} [Field F] (W : WeierstrassCurve (𝓞 F)) (hΔ : W.Δ = 1)

/-- The same Hermitian form from sigma's actual automorphy gives the
previously constructed profile of the actual integral tangent direction. -/
theorem automorphy_tangent_eq_placeProfile (v : InfinitePlace F) :
    π * (latticeForm (lattice W hΔ v) ((coordinateChange W hΔ v).u : ℂ)
      ((coordinateChange W hΔ v).u : ℂ)).re = placeProfile W hΔ v :=
  integral_direction_length _ _

theorem neg_log_automorphy_tangent (v : InfinitePlace F) :
    -Real.log (π * (latticeForm (lattice W hΔ v) ((coordinateChange W hΔ v).u : ℂ)
      ((coordinateChange W hΔ v).u : ℂ)).re) =
      PeriodArithmetic.latticeLogPeriod (lattice W hΔ v) := by
  rw [automorphy_tangent_eq_placeProfile, neg_log_placeProfile]

end PlaceComparison

end RHLean.Geometry.NativeCM.WeierstrassTheta
