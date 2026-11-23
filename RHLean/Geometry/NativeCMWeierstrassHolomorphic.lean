import RHLean.Geometry.NativeCMWeierstrassSectionJet
import RHLean.Geometry.NativeCMWeierstrassGeometricGlue
import RHLean.Geometry.NativeCMWeierstrassThetaAtlasMetric

/-!
# Every regular section is holomorphic along the actual elliptic exponential

The origin-ring and localization calculation is transported by the actual
group-scheme translations. This proves openness of every algebraic chart
inverse image and analyticity of every regular section at every point of
its actual domain. No general holomorphic-uniformization premise is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open Filter PeriodPair
open scoped Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassSectionJet

open WeierstrassCurve SectionPoints

variable (L : PeriodPair) (W : _root_.WeierstrassCurve ℂ) [W.IsElliptic]
  (C : _root_.WeierstrassCurve.VariableChange ℂ)
  (hC : C • W.baseChange ℂ = Weierstrass.latticeCurve L)

/-- The same exponential as a genuine point over the tensor unit. -/
def expOver (z : ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ schemeOver W :=
  Over.homMk (expPoint L W C hC z) (by
    change (ofAffinePoint W ℂ
      (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC z)).left ≫
        toSpec W = 𝟙 (Sp ℂ)
    rw [Over.w]
    exact Spec.map_id _)

@[simp] theorem expOver_left (z : ℂ) : (expOver L W C hC z).left = expPoint L W C hC z := rfl

theorem expOver_add (z w : ℂ) :
    expOver L W C hC (z + w) = expOver L W C hC z * expOver L W C hC w := by
  apply Over.OverMorphism.ext
  change (ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC
    (z + w))).left = _
  rw [map_add]
  exact congrArg Over.Hom.left (ofAffinePoint_add W ℂ _ _)

@[simp] theorem expOver_zero : expOver L W C hC 0 = 1 := by
  rw [← MonObj.one_eq_one]
  exact Over.OverMorphism.ext (expPoint_zero L W C hC)

theorem expOver_surjective : Function.Surjective (expOver L W C hC) := by
  intro p
  have hw : p.left ≫ toSpec W = (specOver ℂ ℂ).hom := by
    rw [Over.w]
    exact (Spec.map_id _).symm
  let p' : specOver ℂ ℂ ⟶ schemeOver W := Over.homMk p.left hw
  obtain ⟨q, hq⟩ := (ofAffinePoint_bijective W ℂ).surjective p'
  obtain ⟨z, hz⟩ := AllPlaceTangentPeriod.exponential_surjective L (W.baseChange ℂ) C hC q
  refine ⟨z, Over.OverMorphism.ext ?_⟩
  change (ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC z)).left = p.left
  rw [hz]
  exact congrArg Over.Hom.left hq

theorem expOver_kernel (z : ℂ) : expOver L W C hC z = 1 ↔ z ∈ L.lattice := by
  rw [← expOver_zero L W C hC]
  constructor
  · intro h
    have e := congrArg Over.Hom.left h
    have e' : ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC z) =
        ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC 0) :=
      Over.OverMorphism.ext e
    have e'' := ofAffinePoint_injective W ℂ e'
    rw [map_zero] at e''
    exact (AllPlaceTangentPeriod.exponential_ker L (W.baseChange ℂ) C hC z).mp e''
  · intro hz
    apply Over.OverMorphism.ext
    change (ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC z)).left =
      (ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC 0)).left
    rw [(AllPlaceTangentPeriod.exponential_ker L (W.baseChange ℂ) C hC z).mpr hz, map_zero]

def translation (z : ℂ) : schemeOver W ≅ schemeOver W :=
  GeometricPoints.rightTranslation (expOver L W C hC z)

theorem expPoint_translate (z w : ℂ) :
    expPoint L W C hC z ≫ (translation L W C hC w).hom.left =
      expPoint L W C hC (z + w) := by
  have h := GeometricPoints.comp_rightTranslation_hom (expOver L W C hC z)
    (expOver L W C hC w)
  rw [show toUnit (𝟙_ (Over (Sp ℂ))) = 𝟙 _ from toUnit_unique _ _,
    Category.id_comp, ← expOver_add L W C hC] at h
  exact congrArg Over.Hom.left h

/-- Every actual algebraic chart has an open inverse image under the
constructed exponential. -/
theorem isOpen_exponential_domain (U : (scheme W).Opens) :
    IsOpen {z | ⊤ ≤ expPoint L W C hC z ⁻¹ᵁ U} := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  let f := (translation L W C hC z).hom.left
  have h0 : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, expPoint_translate, zero_add]
    exact hz
  have hmem := eventually_mem_open L W C hC (f ⁻¹ᵁ U) h0
  have ht : Tendsto (fun x : ℂ => x - z) (𝓝 z) (𝓝 0) :=
    by simpa only [sub_self] using
      (continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℂ => z) z)).tendsto
  filter_upwards [ht.eventually hmem] with x hx
  rw [← Scheme.Hom.comp_preimage, expPoint_translate, sub_add_cancel] at hx
  exact hx

/-- The origin localization proof, translated on the actual group scheme,
proves regular-section analyticity at every point of its genuine domain. -/
theorem analyticAt_eval_section_at (U : (scheme W).Opens)
    (s : Γ(scheme W, U)) {z : ℂ} (hz : ⊤ ≤ expPoint L W C hC z ⁻¹ᵁ U) :
    AnalyticAt ℂ (fun x => value (expPoint L W C hC x) U s) z := by
  let f := (translation L W C hC z).hom.left
  have h0 : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, expPoint_translate, zero_add]
    exact hz
  have ha := (analyticAt_eval_section L W C hC (f ⁻¹ᵁ U) h0
    ((f.app U).hom s)).comp_sub z
  simp only [zero_add] at ha
  apply ha.congr
  exact Filter.Eventually.of_forall fun x => by
    rw [value_comp, expPoint_translate, sub_add_cancel]

theorem holomorphic_regular_sections (U : (scheme W).Opens) (s : Γ(scheme W, U)) :
    IsOpen {z | ⊤ ≤ expPoint L W C hC z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => value (expPoint L W C hC z) U s)
        {z | ⊤ ≤ expPoint L W C hC z ⁻¹ᵁ U} :=
  ⟨isOpen_exponential_domain L W C hC U,
    fun z hz => (analyticAt_eval_section_at L W C hC U s hz).differentiableAt.differentiableWithinAt⟩

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassSectionJet
