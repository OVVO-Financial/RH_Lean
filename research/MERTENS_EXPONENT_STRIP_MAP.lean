import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import «research.MERTENS_EXPONENT_ENVELOPES»

/-!
# Direct Mertens exponent to zeta-strip map

This file proves the arbitrary-exponent FORWARD analytic theorem, starting
with the actual Mobius summatory function. It does not postulate a reciprocal
identity, holomorphy, a zero-free region, RH, or the reverse Perron theorem.

Main result: `MertensGrowthAtMost a` implies that every nontrivial zero has
real part in `[1-a,a]`. Each actual zero also supplies the contrapositive:
a power exponent below either its real part or its reflected real part fails.

The independently defined arithmetic infimum exponent bounds every zero and
its reflection. The converse inequality, and hence equality of the infimum
with the rightmost-zero supremum, is NOT asserted by this module.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators LSeries.notation Topology

/-- Remove the unnecessary energy premise from the classical Abel identity. -/
theorem mellin_eq_moebius_LSeries {s : ℂ} (hs : 1 < s.re) :
    mertensMellinContinuation s = L ↗ArithmeticFunction.moebius s := by
  have hO :
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
        ((ArithmeticFunction.moebius k : ℤ) : ℂ)) =O[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    simpa only [sum_Icc_one_moebius_eq_mertensSummatory] using!
      powerBound_isBigO powerBound_one
  have hS : LSeriesSummable (↗ArithmeticFunction.moebius) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  rw [mertensMellinContinuation, mellin_mertensStep_neg_eq_integral_Ioi_one]
  symm
  rw [LSeries_eq_mul_integral (↗ArithmeticFunction.moebius) zero_le_one hs hS hO]
  apply congrArg (fun z : ℂ => s * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  rfl

/-- The initial reciprocal identity is unconditional on the classical region. -/
theorem reciprocal_identity_classical {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * mertensMellinContinuation s = 1 := by
  rw [mellin_eq_moebius_LSeries hs,
    ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs

/-- An actual power bound gives holomorphy to the right of that exponent. -/
theorem mellin_differentiable_of_powerBound {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) {s : ℂ} (hs : a < s.re) :
    DifferentiableAt ℂ mertensMellinContinuation s := by
  have htop := powerBound_step_isBigO ha hM
  have hbot := mertensStep_isBigO_rpow_zero (s.re + 1)
  have hmellin : DifferentiableAt ℂ (mellin mertensStep) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (a := -a) (b := -s.re - 1) mertensStep_locallyIntegrableOn
    · simpa only [neg_neg] using! htop
    · simp only [neg_re]
      linarith
    · convert hbot using 1
      ring_nf
    · simp only [neg_re]
      linarith
  have hcomp : DifferentiableAt ℂ (fun z : ℂ => mellin mertensStep (-z)) s := by
    simpa only [Function.comp_apply] using!
      hmellin.comp s (differentiableAt_id.neg)
  simpa [mertensMellinContinuation] using! differentiableAt_id.mul hcomp

private def product (s : ℂ) : ℂ := riemannZeta s * mertensMellinContinuation s
private def upper (a : ℝ) : Set ℂ :=
  {s : ℂ | a < s.re} ∩ {s : ℂ | 0 < s.im}
private def lower (a : ℝ) : Set ℂ :=
  {s : ℂ | a < s.re} ∩ {s : ℂ | s.im < 0}
private def leftStrip (a : ℝ) : Set ℂ :=
  {s : ℂ | a < s.re} ∩ {s : ℂ | s.re < 1}

private theorem upper_open (a : ℝ) : IsOpen (upper a) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_const continuous_im)
private theorem lower_open (a : ℝ) : IsOpen (lower a) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im continuous_const)
private theorem leftStrip_open (a : ℝ) : IsOpen (leftStrip a) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
private theorem upper_convex (a : ℝ) : Convex ℝ (upper a) :=
  (convex_halfSpace_re_gt a).inter (convex_halfSpace_im_gt 0)
private theorem lower_convex (a : ℝ) : Convex ℝ (lower a) :=
  (convex_halfSpace_re_gt a).inter (convex_halfSpace_im_lt 0)
private theorem leftStrip_convex (a : ℝ) : Convex ℝ (leftStrip a) :=
  (convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt 1)

private theorem product_analytic {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) {U : Set ℂ} (hU : IsOpen U)
    (hhalf : ∀ z ∈ U, a < z.re) (hone : ∀ z ∈ U, z ≠ 1) :
    AnalyticOnNhd ℂ product U := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
  exact ((differentiableAt_riemannZeta (hone z hz)).mul
    (mellin_differentiable_of_powerBound ha hM (hhalf z hz))).differentiableWithinAt

private theorem product_one_upper {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hM : MertensPowerBound a) :
    Set.EqOn product (fun _ : ℂ => (1 : ℂ)) (upper a) := by
  have hP : AnalyticOnNhd ℂ product (upper a) := by
    apply product_analytic ha hM (upper_open a)
    · intro z hz
      exact hz.1
    · intro z hz hz1
      subst z
      have him := hz.2
      norm_num at him
  have hz0 : (2 : ℂ) + I ∈ upper a := by
    change a < ((2 : ℂ) + I).re ∧ 0 < ((2 : ℂ) + I).im
    constructor
    · norm_num
      linarith
    · norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP analyticOnNhd_const (upper_convex a).isPreconnected hz0 ?_
  have hnhd : {z : ℂ | 1 < z.re} ∈ 𝓝 ((2 : ℂ) + I) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnhd] with z hz
  exact reciprocal_identity_classical hz

private theorem product_one_lower {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hM : MertensPowerBound a) :
    Set.EqOn product (fun _ : ℂ => (1 : ℂ)) (lower a) := by
  have hP : AnalyticOnNhd ℂ product (lower a) := by
    apply product_analytic ha hM (lower_open a)
    · intro z hz
      exact hz.1
    · intro z hz hz1
      subst z
      have him := hz.2
      norm_num at him
  have hz0 : (2 : ℂ) - I ∈ lower a := by
    change a < ((2 : ℂ) - I).re ∧ ((2 : ℂ) - I).im < 0
    constructor
    · norm_num
      linarith
    · norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP analyticOnNhd_const (lower_convex a).isPreconnected hz0 ?_
  have hnhd : {z : ℂ | 1 < z.re} ∈ 𝓝 ((2 : ℂ) - I) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  filter_upwards [hnhd] with z hz
  exact reciprocal_identity_classical hz

private theorem product_one_leftStrip {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hM : MertensPowerBound a) :
    Set.EqOn product (fun _ : ℂ => (1 : ℂ)) (leftStrip a) := by
  have hP : AnalyticOnNhd ℂ product (leftStrip a) := by
    apply product_analytic ha hM (leftStrip_open a)
    · intro z hz
      exact hz.1
    · intro z hz hz1
      subst z
      have hre := hz.2
      norm_num at hre
  let z0 : ℂ := (((a + 1) / 2 : ℝ) : ℂ) + I
  have hz0strip : z0 ∈ leftStrip a := by
    change a < z0.re ∧ z0.re < 1
    simp only [z0, add_re, ofReal_re, I_re, add_zero]
    constructor <;> linarith
  have hz0upper : z0 ∈ upper a := by
    change a < z0.re ∧ 0 < z0.im
    simp only [z0, add_re, ofReal_re, I_re, add_zero, add_im, ofReal_im, I_im, zero_add]
    constructor <;> linarith
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    hP analyticOnNhd_const (leftStrip_convex a).isPreconnected hz0strip ?_
  have hnhd : upper a ∈ 𝓝 z0 := (upper_open a).mem_nhds hz0upper
  filter_upwards [hnhd] with z hz
  exact product_one_upper ha ha1 hM hz

/-- The reciprocal identity on the full exponent half-plane, excluding the pole. -/
theorem reciprocal_identity_of_powerBound {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) {s : ℂ} (hs : a < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * mertensMellinContinuation s = 1 := by
  by_cases hgt : 1 < s.re
  · exact reciprocal_identity_classical hgt
  have ha1 : a < 1 := lt_of_lt_of_le hs (le_of_not_gt hgt)
  by_cases hlt : s.re < 1
  · exact product_one_leftStrip ha ha1 hM ⟨hs, hlt⟩
  have hre : s.re = 1 := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
  have himne : s.im ≠ 0 := by
    intro him
    apply hs1
    apply Complex.ext
    · exact hre
    · exact him
  rcases lt_or_gt_of_ne himne with himlt | himgt
  · exact product_one_lower ha ha1 hM ⟨hs, himlt⟩
  · exact product_one_upper ha ha1 hM ⟨hs, himgt⟩

/-- Direct arithmetic-growth to analytic-nonvanishing theorem. -/
theorem zeta_ne_zero_of_powerBound {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) {s : ℂ} (hs : a < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hid := reciprocal_identity_of_powerBound ha hM hs hs1
  rw [hz, zero_mul] at hid
  exact zero_ne_one hid

/-- Only actual zeros in the open critical strip are called nontrivial here. -/
def NontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- Closed endpoints; neither endpoint is asserted to contain a zero. -/
def ZerosInSymmetricStrip (a : ℝ) : Prop :=
  ∀ ρ : ℂ, NontrivialZetaZero ρ → 1 - a ≤ ρ.re ∧ ρ.re ≤ a

/-- Functional-equation reflection of an actual nontrivial zero. -/
theorem nontrivialZero_one_sub {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    NontrivialZetaZero (1 - ρ) := by
  obtain ⟨hz, hpos, hlt⟩ := hρ
  have hρ0 : ρ ≠ 0 := by intro h; subst ρ; norm_num at hpos
  have href0 : 1 - ρ ≠ 0 := by
    intro h
    have heq : ρ = 1 := (sub_eq_zero.mp h).symm
    rw [heq] at hlt
    norm_num at hlt
  have hGamma : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hc : completedRiemannZeta ρ = 0 := by
    have hd : completedRiemannZeta ρ / Gammaℝ ρ = 0 := by
      rw [← riemannZeta_def_of_ne_zero hρ0, hz]
    simpa [hGamma] using! hd
  have hrc : completedRiemannZeta (1 - ρ) = 0 := by
    rw [completedRiemannZeta_one_sub ρ, hc]
  refine ⟨?_, ?_, ?_⟩
  · rw [riemannZeta_def_of_ne_zero href0, hrc]
    simp
  · simp only [sub_re, one_re]
    linarith
  · simp only [sub_re, one_re]
    linarith

/-- Every exact power bound is an upper bound for each zero's real part. -/
theorem zero_re_le_of_powerBound {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    ρ.re ≤ a := by
  by_contra hnot
  have hs1 : ρ ≠ 1 := by intro h; rw [h] at hρ; norm_num [NontrivialZetaZero] at hρ
  exact (zeta_ne_zero_of_powerBound ha hM (lt_of_not_ge hnot) hs1) hρ.1

/-- Exact power control gives both walls of the critical strip. -/
theorem strip_of_powerBound {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensPowerBound a) : ZerosInSymmetricStrip a := by
  intro ρ hρ
  have hr := zero_re_le_of_powerBound ha hM hρ
  have hl := zero_re_le_of_powerBound ha hM (nontrivialZero_one_sub hρ)
  simp only [sub_re, one_re] at hl
  exact ⟨by linarith, hr⟩

/-- No endpoint-attainment assumption is needed when passing to the infimum. -/
theorem zero_re_le_growthExponent {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    ρ.re ≤ mertensGrowthExponent := by
  apply le_csInf admissibleExponents_nonempty
  intro a ha
  exact zero_re_le_of_powerBound ha.1 ha.2 hρ

/-- The arithmetic infimum supplies a direct symmetric zero enclosure. -/
theorem strip_at_growthExponent : ZerosInSymmetricStrip mertensGrowthExponent := by
  intro ρ hρ
  have hr := zero_re_le_growthExponent hρ
  have hl := zero_re_le_growthExponent (nontrivialZero_one_sub hρ)
  simp only [sub_re, one_re] at hl
  exact ⟨by linarith, hr⟩

/-- The principal epsilon-loss forward map requested by the exponent picture. -/
theorem strip_of_growthAtMost {a : ℝ} (ha : 0 ≤ a)
    (hM : MertensGrowthAtMost a) : ZerosInSymmetricStrip a := by
  have hle := (growthAtMost_iff_growthExponent_le ha).mp hM
  intro ρ hρ
  obtain ⟨hl, hr⟩ := strip_at_growthExponent ρ hρ
  exact ⟨by linarith, by linarith⟩

/-- A hypothetical zero rules out every smaller power exponent. -/
theorem not_powerBound_of_zero_right {a : ℝ} (ha : 0 ≤ a)
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) (hgap : a < ρ.re) :
    ¬ MertensPowerBound a := by
  intro hM
  exact (not_le_of_gt hgap) (zero_re_le_of_powerBound ha hM hρ)

/-- The left-hand zero acts through its right-hand reflected exponent. -/
theorem not_powerBound_of_zero_left {a : ℝ} (ha : 0 ≤ a)
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) (hgap : a < 1 - ρ.re) :
    ¬ MertensPowerBound a := by
  apply not_powerBound_of_zero_right ha (nontrivialZero_one_sub hρ)
  simpa only [sub_re, one_re] using! hgap

/-- A zero outside the predicted strip contradicts exponent-level control. -/
theorem not_growthAtMost_of_zero_outside {a : ℝ} (ha : 0 ≤ a)
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ)
    (hout : ρ.re < 1 - a ∨ a < ρ.re) : ¬ MertensGrowthAtMost a := by
  intro hM
  obtain ⟨hl, hr⟩ := strip_of_growthAtMost ha hM ρ hρ
  rcases hout with h | h
  · exact (not_le_of_gt h) hl
  · exact (not_le_of_gt h) hr

/-- Any supplied actual nontrivial zero forces a growth exponent at least half.
The existence of such a zero is explicit here, not an imported numerical axiom. -/
theorem half_le_growthExponent_of_zero {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    (1 : ℝ) / 2 ≤ mertensGrowthExponent := by
  obtain ⟨hl, hr⟩ := strip_at_growthExponent ρ hρ
  linarith

/-- Critical exponent control puts every nontrivial zero on the critical line. -/
theorem criticalLine_of_growth_half (hM : MertensGrowthAtMost ((1 : ℝ) / 2))
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) : ρ.re = (1 : ℝ) / 2 := by
  obtain ⟨hl, hr⟩ := strip_of_growthAtMost (by norm_num : (0 : ℝ) ≤ 1 / 2) hM ρ hρ
  linarith

/-- Seven-eighths is an input exponent, not an unconditional new bound. -/
theorem sevenEighths_strip (hM : MertensGrowthAtMost ((7 : ℝ) / 8))
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    (1 : ℝ) / 8 ≤ ρ.re ∧ ρ.re ≤ (7 : ℝ) / 8 := by
  have h := strip_of_growthAtMost (by norm_num : (0 : ℝ) ≤ 7 / 8) hM ρ hρ
  norm_num at h ⊢
  exact h

end RHLean.Analysis.MertensExponent
