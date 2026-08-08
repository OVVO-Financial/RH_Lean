import Mathlib
import RHLean.Analysis.MertensMellinLSeriesBridge

/-!
# Analytic uniqueness for the Mertens Mellin reciprocal identity

The overlap identity `ζ(s) * F(s) = 1` is proved first on `Re(s) > 1`.
The Mertens energy criterion makes `F` holomorphic on `Re(s) > 1/2`, while
Riemann zeta is holomorphic away from its pole at `1`.

Rather than formalizing connectedness of the punctured half-plane directly, we
propagate the identity over three convex pole-free regions:

* `Re(s) > 1/2` and `Im(s) > 0`,
* `Re(s) > 1/2` and `Im(s) < 0`,
* `1/2 < Re(s) < 1`.

Together with the original `Re(s) > 1` overlap these regions cover every point
to the right of the critical line except the pole.  This gives the required
right-half-plane zeta nonvanishing as an immediate algebraic corollary.
-/

noncomputable section

namespace RHLean.Analysis

open Complex Set Filter

private def mertensUpperRegion : Set ℂ :=
  {z : ℂ | (1 : ℝ) / 2 < z.re} ∩ {z : ℂ | 0 < z.im}

private def mertensLowerRegion : Set ℂ :=
  {z : ℂ | (1 : ℝ) / 2 < z.re} ∩ {z : ℂ | z.im < 0}

private def mertensLeftStrip : Set ℂ :=
  {z : ℂ | (1 : ℝ) / 2 < z.re} ∩ {z : ℂ | z.re < 1}

private theorem mertensUpperRegion_isOpen : IsOpen mertensUpperRegion := by
  unfold mertensUpperRegion
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_const continuous_im)

private theorem mertensLowerRegion_isOpen : IsOpen mertensLowerRegion := by
  unfold mertensLowerRegion
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im continuous_const)

private theorem mertensLeftStrip_isOpen : IsOpen mertensLeftStrip := by
  unfold mertensLeftStrip
  exact (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)

private theorem mertensUpperRegion_isPreconnected : IsPreconnected mertensUpperRegion := by
  unfold mertensUpperRegion
  exact ((convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_im_gt 0)).isPreconnected

private theorem mertensLowerRegion_isPreconnected : IsPreconnected mertensLowerRegion := by
  unfold mertensLowerRegion
  exact ((convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_im_lt 0)).isPreconnected

private theorem mertensLeftStrip_isPreconnected : IsPreconnected mertensLeftStrip := by
  unfold mertensLeftStrip
  exact ((convex_halfSpace_re_gt ((1 : ℝ) / 2)).inter
    (convex_halfSpace_re_lt 1)).isPreconnected

private theorem riemannZeta_ne_one_of_mem_upper {z : ℂ}
    (hz : z ∈ mertensUpperRegion) : z ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hzIm : 0 < z.im := hz.2
  simp at him
  linarith

private theorem riemannZeta_ne_one_of_mem_lower {z : ℂ}
    (hz : z ∈ mertensLowerRegion) : z ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hzIm : z.im < 0 := hz.2
  simp at him
  linarith

private theorem riemannZeta_ne_one_of_mem_strip {z : ℂ}
    (hz : z ∈ mertensLeftStrip) : z ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  have hzRe : z.re < 1 := hz.2
  simp at hre
  linarith

private theorem analyticOnNhd_reciprocalProduct_upper
    (hM : MertensEnergyBoundedStatement) :
    AnalyticOnNhd ℂ
      (fun z => riemannZeta z * mertensMellinContinuation z)
      mertensUpperRegion := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    mertensUpperRegion_isOpen
  exact ((differentiableAt_riemannZeta
      (riemannZeta_ne_one_of_mem_upper hz)).mul
    (differentiableAt_mertensMellinContinuation hM hz.1)).differentiableWithinAt

private theorem analyticOnNhd_reciprocalProduct_lower
    (hM : MertensEnergyBoundedStatement) :
    AnalyticOnNhd ℂ
      (fun z => riemannZeta z * mertensMellinContinuation z)
      mertensLowerRegion := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    mertensLowerRegion_isOpen
  exact ((differentiableAt_riemannZeta
      (riemannZeta_ne_one_of_mem_lower hz)).mul
    (differentiableAt_mertensMellinContinuation hM hz.1)).differentiableWithinAt

private theorem analyticOnNhd_reciprocalProduct_strip
    (hM : MertensEnergyBoundedStatement) :
    AnalyticOnNhd ℂ
      (fun z => riemannZeta z * mertensMellinContinuation z)
      mertensLeftStrip := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    mertensLeftStrip_isOpen
  exact ((differentiableAt_riemannZeta
      (riemannZeta_ne_one_of_mem_strip hz)).mul
    (differentiableAt_mertensMellinContinuation hM hz.1)).differentiableWithinAt

private theorem reciprocalProduct_eq_one_upper
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn
      (fun z => riemannZeta z * mertensMellinContinuation z)
      (fun _ : ℂ => (1 : ℂ)) mertensUpperRegion := by
  let z0 : ℂ := 2 + I
  have hz0 : z0 ∈ mertensUpperRegion := by
    dsimp [z0, mertensUpperRegion]
    norm_num
  have hseed :
      (fun z => riemannZeta z * mertensMellinContinuation z) =ᶠ[𝓝 z0]
        (fun _ : ℂ => (1 : ℂ)) := by
    have hright : {z : ℂ | 1 < z.re} ∈ 𝓝 z0 :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        dsimp [z0]
        norm_num)
    filter_upwards [hright] with z hz
    exact riemannZeta_mul_mertensMellinContinuation_eq_one hM hz
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ)
    (analyticOnNhd_reciprocalProduct_upper hM)
    analyticOnNhd_const
    mertensUpperRegion_isPreconnected hz0 hseed

private theorem reciprocalProduct_eq_one_lower
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn
      (fun z => riemannZeta z * mertensMellinContinuation z)
      (fun _ : ℂ => (1 : ℂ)) mertensLowerRegion := by
  let z0 : ℂ := 2 - I
  have hz0 : z0 ∈ mertensLowerRegion := by
    dsimp [z0, mertensLowerRegion]
    norm_num
  have hseed :
      (fun z => riemannZeta z * mertensMellinContinuation z) =ᶠ[𝓝 z0]
        (fun _ : ℂ => (1 : ℂ)) := by
    have hright : {z : ℂ | 1 < z.re} ∈ 𝓝 z0 :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        dsimp [z0]
        norm_num)
    filter_upwards [hright] with z hz
    exact riemannZeta_mul_mertensMellinContinuation_eq_one hM hz
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ)
    (analyticOnNhd_reciprocalProduct_lower hM)
    analyticOnNhd_const
    mertensLowerRegion_isPreconnected hz0 hseed

private theorem reciprocalProduct_eq_one_strip
    (hM : MertensEnergyBoundedStatement) :
    Set.EqOn
      (fun z => riemannZeta z * mertensMellinContinuation z)
      (fun _ : ℂ => (1 : ℂ)) mertensLeftStrip := by
  let z0 : ℂ := (3 : ℂ) / 4 + I
  have hz0Strip : z0 ∈ mertensLeftStrip := by
    dsimp [z0, mertensLeftStrip]
    norm_num
  have hz0Upper : z0 ∈ mertensUpperRegion := by
    dsimp [z0, mertensUpperRegion]
    norm_num
  have hupper := reciprocalProduct_eq_one_upper hM
  have hseed :
      (fun z => riemannZeta z * mertensMellinContinuation z) =ᶠ[𝓝 z0]
        (fun _ : ℂ => (1 : ℂ)) := by
    have hmem : mertensUpperRegion ∈ 𝓝 z0 :=
      mertensUpperRegion_isOpen.mem_nhds hz0Upper
    filter_upwards [hmem] with z hz
    exact hupper hz
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (𝕜 := ℂ)
    (analyticOnNhd_reciprocalProduct_strip hM)
    analyticOnNhd_const
    mertensLeftStrip_isPreconnected hz0Strip hseed

/-- The reciprocal identity propagated to every point strictly right of the
critical line except the zeta pole. -/
theorem riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * mertensMellinContinuation s = 1 := by
  by_cases hright : 1 < s.re
  · exact riemannZeta_mul_mertensMellinContinuation_eq_one hM hright
  by_cases hleft : s.re < 1
  · exact reciprocalProduct_eq_one_strip hM ⟨hs, hleft⟩
  have hre : s.re = 1 := by linarith
  have him : s.im ≠ 0 := by
    intro hzero
    apply hs1
    apply Complex.ext
    · simpa [hre]
    · simpa [hzero]
  by_cases hpos : 0 < s.im
  · exact reciprocalProduct_eq_one_upper hM ⟨hs, hpos⟩
  · have hneg : s.im < 0 := by
      have hle : s.im ≤ 0 := le_of_not_gt hpos
      exact lt_of_le_of_ne hle him
    exact reciprocalProduct_eq_one_lower hM ⟨hs, hneg⟩

/-- In particular, zeta has no zero strictly to the right of the critical line. -/
theorem riemannZeta_ne_zero_of_half_lt_re
    (hM : MertensEnergyBoundedStatement) {s : ℂ}
    (hs : (1 : ℝ) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hprod :=
    riemannZeta_mul_mertensMellinContinuation_eq_one_of_half_lt_re hM hs hs1
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

end RHLean.Analysis
