import RHLean.Geometry.NativeCMWeierstrassThetaAtlasMetric
import RHLean.Geometry.NativeCMWeierstrassSectionJet
import RHLean.Geometry.NativeCMLineBundleGerms

/-!
# The actual sigma metric on a signed pullback atlas

The metric is the signed product of the actual seed chart metrics. Its
transition factor is evaluated from the literal LinComb transition unit,
including its pullback and restriction maps. This proves chart
independence, positivity, and invariance under every seed period.

This is a native chart calculation. The application to the represented
Serre scheme supplies its actual point and coordinate maps separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex PeriodPair AlgebraicGeometry CategoryTheory
open scoped Classical BigOperators ComplexConjugate Real

namespace RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

variable {X Y : Scheme.{0}}

theorem evalPt_unit_zpow (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) (n : ℤ) :
    evalPt x U h (u ^ n : Γ(X, U)ˣ) = (evalPt x U h (u : Γ(X, U))) ^ n := by
  change ((Units.map (evalPt x U h) (u ^ n) : ℂˣ) : ℂ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem evalPt_res_pullU (x : Sp ℂ ⟶ Y) (f : Y ⟶ X) (U : X.Opens)
    {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    evalPt x V h (res e (pullU f U u) : Γ(Y, V)) =
      evalPt (x ≫ f) U h' (u : Γ(X, U)) := by
  change evalPt x V h (resG Y e ((f.app U).hom (u : Γ(X, U)))) = _
  rw [evalPt_res x e (h.trans (x.preimage_mono e)) h]
  exact (evalPt_comp x f U h' (h.trans (x.preimage_mono e)) _).symm

/-- Evaluation retains the actual restricted and pulled transition units. -/
theorem evalPt_linComb_transition (L : LB X) {K : Type} [Fintype K]
    (f : K → (Y ⟶ X)) (ε : K → ℤ) (i j : K → L.ι) (x : Sp ℂ ⟶ Y)
    (h : ⊤ ≤ x ⁻¹ᵁ ((LB.LinComb L f ε).U i ⊓ (LB.LinComb L f ε).U j)) :
    evalPt x _ h ((LB.LinComb L f ε).g i j :
      Γ(Y, (LB.LinComb L f ε).U i ⊓ (LB.LinComb L f ε).U j)) =
      ∏ k, (evalPt x _ h
        (res (LB.wchart_inter_le L f i j k)
          (pullU (f k) _ (L.g (i k) (j k))) : Γ(Y, _))) ^ ε k := by
  change evalPt x _ h ((∏ k, (res (LB.wchart_inter_le L f i j k)
    (pullU (f k) _ (L.g (i k) (j k)))) ^ ε k) : Γ(Y, _)ˣ) = _
  rw [Units.val_prod, map_prod]
  exact Finset.prod_congr rfl fun k _ => evalPt_unit_zpow x _ h _ (ε k)

end RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

namespace RHLean.Geometry.NativeCM.WeierstrassTheta

open SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.SectionPoints
open Weierstrass

variable {R : Type} [CommRing R] [Algebra R ℂ] (W : _root_.WeierstrassCurve R)
    (L : PeriodPair) (C : _root_.WeierstrassCurve.VariableChange ℂ)

omit [Algebra R ℂ] in
theorem chartNormSq_scalar (i : (originLB W).ι) (z c : ℂ) :
    chartNormSq W L C i z c = ‖c‖ ^ 2 * chartNormSq W L C i z 1 := by
  simp only [chartNormSq, fiberNormSq, div_eq_mul_inv, norm_mul, mul_pow, one_mul]
  ring

theorem norm_signed_product_sq {K : Type} [Fintype K] (f : K → ℂ) (ε : K → ℤ) :
    ‖∏ k, f k ^ ε k‖ ^ 2 = ∏ k, (‖f k‖ ^ 2) ^ ε k := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_zpow, pow_two, ← mul_zpow, ← pow_two]

variable {Z K : Type} [Fintype K] (l : K → Z → ℂ) (ε : K → ℤ)

/-- The squared norm is the actual signed product of seed chart metrics. -/
def signedChartNormSq (j : K → (originLB W).ι) (z : Z) (c : ℂ) : ℝ :=
  ‖c‖ ^ 2 * ∏ k, (chartNormSq W L C (j k) (l k z) 1) ^ ε k

def signedFrame (j : K → (originLB W).ι) (z : Z) : ℂ :=
  ∏ k, (atlasFrame W L C (j k) (l k z)) ^ ε k

/-- The signed Gaussian is computed from the literal product metric;
its quadratic term is not an independently chosen form. -/
theorem signedChartNormSq_gaussian (j : K → (originLB W).ι) (z : Z) (c : ℂ) :
    signedChartNormSq W L C l ε j z c =
      ‖c / signedFrame W L C l ε j z‖ ^ 2 *
        Real.exp (-π * ∑ k, (ε k : ℝ) * (latticeForm L (l k z) (l k z)).re) := by
  have hn : (∏ k, (‖(atlasFrame W L C (j k) (l k z))⁻¹‖ ^ 2) ^ ε k) =
      ‖(signedFrame W L C l ε j z)⁻¹‖ ^ 2 := by
    rw [← norm_signed_product_sq]
    congr 2
    simp only [signedFrame, Finset.prod_inv_distrib, inv_zpow]
  have he : (∏ k, (Real.exp (-π * (latticeForm L (l k z) (l k z)).re)) ^ ε k) =
      Real.exp (-π * ∑ k, (ε k : ℝ) * (latticeForm L (l k z) (l k z)).re) := by
    have hz (x : ℝ) (n : ℤ) : Real.exp x ^ n = Real.exp (n * x) := by
      rw [← Real.rpow_intCast, ← Real.exp_mul, mul_comm]
    simp_rw [hz]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [signedChartNormSq, chartNormSq, fiberNormSq, one_div,
    mul_zpow, Finset.prod_mul_distrib]
  rw [hn, he]
  simp only [div_eq_mul_inv, norm_mul, mul_pow]
  ring

omit [Algebra R ℂ] in
theorem signedChartNormSq_zero (j : K → (originLB W).ι) (z : Z) :
    signedChartNormSq W L C l ε j z 0 = 0 := by
  simp only [signedChartNormSq, norm_zero, zero_pow two_ne_zero, zero_mul]

variable (hC : C • W.baseChange ℂ = latticeCurve L)
    {Y : Scheme.{0}} (f : K → (Y ⟶ scheme W)) (p : Z → (Sp ℂ ⟶ Y))
    (hp : ∀ k z, p z ≫ f k = (analyticPoint W L C hC (l k z)).left)

include hp in
theorem signedChartNormSq_pos (j : K → (originLB W).ι) (z : Z) {c : ℂ}
    (h : ⊤ ≤ p z ⁻¹ᵁ (LB.LinComb (originLB W) f ε).U j) (hc : c ≠ 0) :
    0 < signedChartNormSq W L C l ε j z c := by
  apply mul_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hc))
  apply Finset.prod_pos
  intro k _
  apply zpow_pos
  have h' : ⊤ ≤ (analyticPoint W L C hC (l k z)).left ⁻¹ᵁ (originLB W).U (j k) := by
    rw [← hp k z, Scheme.Hom.comp_preimage]
    exact h.trans ((p z).preimage_mono (LB.wchart_le (originLB W) f j k))
  exact chartNormSq_pos W L C hC (j k) h' one_ne_zero

include hp in
/-- The actual transition unit of the original signed atlas is an isometry. -/
theorem signedChartNormSq_transition (i j : K → (originLB W).ι) (z : Z) (c : ℂ)
    (h : ⊤ ≤ p z ⁻¹ᵁ ((LB.LinComb (originLB W) f ε).U i ⊓
      (LB.LinComb (originLB W) f ε).U j)) :
    signedChartNormSq W L C l ε i z
      (evalPt (p z) _ h ((LB.LinComb (originLB W) f ε).g i j : Γ(Y, _)) * c) =
        signedChartNormSq W L C l ε j z c := by
  let g (k : K) : ℂ := evalPt (p z) _ h
    (res (LB.wchart_inter_le (originLB W) f i j k)
      (pullU (f k) _ ((originLB W).g (i k) (j k))) : Γ(Y, _))
  have hg (k : K) :
      ‖g k‖ ^ 2 * chartNormSq W L C (i k) (l k z) 1 =
        chartNormSq W L C (j k) (l k z) 1 := by
    have hpk : ⊤ ≤ (p z ≫ f k) ⁻¹ᵁ
        ((originLB W).U (i k) ⊓ (originLB W).U (j k)) := by
      rw [Scheme.Hom.comp_preimage]
      exact h.trans ((p z).preimage_mono (LB.wchart_inter_le (originLB W) f i j k))
    have hq : ⊤ ≤ (analyticPoint W L C hC (l k z)).left ⁻¹ᵁ
        ((originLB W).U (i k) ⊓ (originLB W).U (j k)) := hp k z ▸ hpk
    have he : g k = evalPt (analyticPoint W L C hC (l k z)).left _ hq
        ((originLB W).g (i k) (j k) : Γ(scheme W, _)) := by
      have he := evalPt_res_pullU (p z) (f k) _
        (LB.wchart_inter_le (originLB W) f i j k) h hpk ((originLB W).g (i k) (j k))
      rw [hp k z] at he
      exact he
    have ht := chartNormSq_transition W L C hC (i k) (j k) (l k z) 1 hq
    rw [← he, mul_one, chartNormSq_scalar] at ht
    exact ht
  rw [signedChartNormSq, signedChartNormSq, norm_mul, mul_pow,
    evalPt_linComb_transition, norm_signed_product_sq]
  change (∏ k, (‖g k‖ ^ 2) ^ ε k) * ‖c‖ ^ 2 *
    (∏ k, (chartNormSq W L C (i k) (l k z) 1) ^ ε k) = _
  calc
    _ = ‖c‖ ^ 2 * ∏ k,
        ((‖g k‖ ^ 2) ^ ε k * (chartNormSq W L C (i k) (l k z) 1) ^ ε k) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, hg]

/-- Every seed period preserves the signed pullback metric. -/
theorem signedChartNormSq_period (j : K → (originLB W).ι) (z z' : Z)
    (w : K → ℂ) (hw : ∀ k, w k ∈ L.lattice)
    (hz : ∀ k, l k z' = l k z + w k) (c : ℂ) :
    signedChartNormSq W L C l ε j z' c = signedChartNormSq W L C l ε j z c := by
  unfold signedChartNormSq
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hz, chartNormSq_period W L C (j k) (hw k)]

end RHLean.Geometry.NativeCM.WeierstrassTheta

end
