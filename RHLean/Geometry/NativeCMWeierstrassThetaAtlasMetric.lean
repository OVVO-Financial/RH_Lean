import RHLean.Geometry.NativeCMWeierstrassThetaAtlas

/-!
# The actual origin-bundle metric descends through its algebraic charts

The squared norm of a local fiber coordinate is the sigma norm after
conversion by the explicitly constructed analytic frame. The genuine
algebraic transition units preserve it. It is positive on every nonzero
fiber, unchanged by a period, and evaluates the actual canonical section
to the proved periodic sigma norm. The associated automorphy form retains
the exact original tangent scale at every infinite place.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex PeriodPair AlgebraicGeometry CategoryTheory
open scoped ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.SectionPoints
open Weierstrass AllPlaceTangentPeriod

variable {R : Type} [CommRing R] [Algebra R ℂ] (W : WeierstrassCurve R)
  (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ)
  (hC : C • W.baseChange ℂ = latticeCurve L)

theorem analyticPoint_period {w : ℂ} (hw : w ∈ L.lattice) (z : ℂ) :
    analyticPoint W L C hC (z + w) = analyticPoint W L C hC z := by
  rw [analyticPoint, analyticPoint, map_add,
    (exponential_ker L (W.baseChange ℂ) C hC w).mpr hw, add_zero]

/-- Squared norm of a fiber coordinate in an actual origin-bundle chart. -/
def chartNormSq (i : (originLB W).ι) (z c : ℂ) : ℝ :=
  fiberNormSq L z (c / atlasFrame W L C i z)

theorem chartNormSq_pos (i : (originLB W).ι) {z c : ℂ}
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i) (hc : c ≠ 0) :
    0 < chartNormSq W L C i z c :=
  fiberNormSq_pos L (div_ne_zero hc (atlasFrame_ne_zero W L C hC i h))

/-- The transition unit of the original algebraic bundle is an isometry. -/
theorem chartNormSq_transition (i j : (originLB W).ι) (z c : ℂ)
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ
      ((originLB W).U i ⊓ (originLB W).U j)) :
    chartNormSq W L C i z
      (evalPt (analyticPoint W L C hC z).left ((originLB W).U i ⊓ (originLB W).U j) h
        ((originLB W).g i j : Γ(scheme W, (originLB W).U i ⊓ (originLB W).U j)) * c) =
      chartNormSq W L C j z c := by
  have hu := ((originLB W).g i j).isUnit.map
    (evalPt (analyticPoint W L C hC z).left ((originLB W).U i ⊓ (originLB W).U j) h)
  rw [chartNormSq, chartNormSq, atlasFrame_compat W L C hC i j z h,
    mul_div_mul_left _ _ hu.ne_zero]

omit [Algebra R ℂ] in
/-- Lattice translations give the same metric on the same scheme point. -/
theorem chartNormSq_period (i : (originLB W).ι) {w : ℂ} (hw : w ∈ L.lattice)
    (z c : ℂ) : chartNormSq W L C i (z + w) c = chartNormSq W L C i z c := by
  rw [chartNormSq, chartNormSq, atlasFrame_period W L C i hw]
  have e : c / (atlasFrame W L C i z / multiplier L w z) =
      multiplier L w z * (c / atlasFrame W L C i z) := by
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [e, fiberNormSq_multiplier]

/-- The actual algebraic origin section has the computed periodic norm. -/
theorem chartNormSq_originSec (i : (originLB W).ι) (z : ℂ)
    (h : ⊤ ≤ (analyticPoint W L C hC z).left ⁻¹ᵁ (originLB W).U i) :
    chartNormSq W L C i z
      (evalPt (analyticPoint W L C hC z).left ((originLB W).U i) h ((originSec W).f i)) =
      sigmaNormSq L z := by
  rw [chartNormSq, atlas_section_factorization W L C hC i z h,
    mul_div_cancel_right₀ _ (atlasFrame_ne_zero W L C hC i h)]
  rfl

end RHLean.Geometry.NativeCM.WeierstrassTheta
