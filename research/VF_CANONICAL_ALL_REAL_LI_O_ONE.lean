import Mathlib
import «research.VF_MID_LI_UNIFORM_QUADRATURE»

/-!
# All-real uniform VF midpoint / Li_2 quadrature

This closes a DOCUMENTATION / THEOREM ASSEMBLY omission, not an
arithmetic number-theory conjecture. The primary repository already proved:

  (1) |vfMid(R^2) - Li_2(R^2)| <= C_square for every R>=2,
  (2) |vfMidLiveQuadratureError R x| <= C_tile for the ENTIRE live band,
  (3) exact Li-error = completed-square error + live-band error.

Putting the exact three existing theorems together proves
  |vfMid(x) - Li_2(x)| <= C_square + C_tile
UNIFORMLY for ALL REAL x>=4, not just square endpoints.

The Li convention is Li_2(x) = integral_2^x dt/log t.
This is independent of all prime-distribution hypotheses.
-/

noncomputable section

namespace RHLean.Analysis

/-- One explicit, finite all-real quadrature constant, assembled from the
already proved SUMMABLE full-band errors and UNIFORM live-band error. -/
def vfMidLiAllRealUniformConstant : ℝ :=
  vfMidLiSquareEndpointUniformConstant + vfMidTileQuadratureBound

theorem vfMidLiAllRealUniformConstant_nonneg :
    0 ≤ vfMidLiAllRealUniformConstant := by
  unfold vfMidLiAllRealUniformConstant
  exact add_nonneg vfMidLiSquareEndpointUniformConstant_nonneg
    vfMidTileQuadratureBound_nonneg

/-- UNCONDITIONAL all-real O(1). The older file only declared
vfMidLiRootBounded, but its own live-band bound and the newer
square-endpoint summability already imply this stronger theorem. -/
theorem abs_vfMidLiError_le_uniform_allReal
    {x : ℝ} (hx : 4 ≤ x) :
    |vfMidLiError x| ≤ vfMidLiAllRealUniformConstant := by
  let R : ℕ := vfMidSquareRootIndex x
  have hb :
      2 ≤ R ∧ (R : ℝ) ^ 2 ≤ x ∧
        x ≤ (((R + 1 : ℕ) : ℝ) ^ 2) ∧
        (R : ℝ) ≤ Real.sqrt x :=
    vfMidSquareRootIndex_bounds hx
  rcases hb with ⟨hR, hxl, hxu, _⟩
  have hsquare :
      |vfMidLiError ((R : ℝ) ^ 2)| ≤
        vfMidLiSquareEndpointUniformConstant :=
    abs_vfMidLiError_sq_le_uniform hR
  have hlive :
      |vfMidLiveQuadratureError R x| ≤
        vfMidTileQuadratureBound :=
    abs_vfMidLiveQuadratureError_le hR hxl hxu
  rw [vfMidLiError_eq_sq_add_live hx]
  exact (abs_add_le _ _).trans (add_le_add hsquare hlive)

/-- Entire real continuum, not a discrete-endpoint-only result. -/
def VFMidLiAllRealUniformBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 4 ≤ x →
      |vfMid x - vfMidLogarithmicIntegralFromTwo x| ≤ C

theorem vfMidLiAllRealUniformBounded :
    VFMidLiAllRealUniformBoundedStatement := by
  refine ⟨vfMidLiAllRealUniformConstant,
    vfMidLiAllRealUniformConstant_nonneg, ?_⟩
  intro x hx
  simpa [vfMidLiError] using!
    abs_vfMidLiError_le_uniform_allReal hx

end RHLean.Analysis
