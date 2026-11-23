import RHLean.Analysis.AlpogeNativeWindowMellin
import RHLean.Analysis.AlpogeSquareClockSignedHistorySampling
import RHLean.Analysis.AlpogeWindowLandauCriterion

/-!
# Zeta zeros from one-sided windows of the native signed prime-power sum

The divided difference of the logarithmic derivative of Mathlib's entire
`riemannZeta₁` removes both principal parts at one. At a zero of multiplicity
`m`, the transform has residue `-m / (ρ * (ρ - 1))`.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace RHLean.Analysis

local notation "γ₀" => Real.eulerMascheroniConstant

def alpogeNativeGzTransform (s : ℂ) : ℂ :=
  (1 + (γ₀ : ℂ) - dslope (logDeriv riemannZeta₁) 1 s) / s

private theorem zeta₁_ne_zero_iff (s : ℂ) : riemannZeta₁ s ≠ 0 ↔ riemannZeta s ≠ 0 := by
  by_cases hs : s = 1
  · simp [hs, riemannZeta_one_ne_zero]
  rw [riemannZeta_eq_inv_sub_mul hs]
  simp [sub_ne_zero.mpr hs]

private theorem transform_off_one {s : ℂ} (hs : s ≠ 1) :
    alpogeNativeGzTransform s =
      (1 + (γ₀ : ℂ) - (logDeriv riemannZeta₁ s - γ₀) / (s - 1)) / s := by
  simp [alpogeNativeGzTransform, dslope_of_ne _ hs, slope_def_field, logDeriv_apply]

theorem alpogeNativeGzTransform_laplace {s : ℂ} (hs : 1 < s.re) :
    alpogeNativeGzTransform s =
      ∫ u in Ioi (0 : ℝ), (alpogeNativeGzArithmetic (Real.exp u) : ℂ) * cexp (-s * u) := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have hs0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hz := (zeta₁_ne_zero_iff s).2 (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [alpogeNativeLaplace_eq_mellin (fun y => (alpogeNativeGzArithmetic y : ℂ)),
    alpogeNativeGzArithmetic_mellin s hs, transform_off_one hs1, logDeriv_apply,
    deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1, riemannZeta_eq_inv_sub_mul hs1]
  field_simp [hz, hs0, sub_ne_zero.mpr hs1]
  ring

theorem alpogeNativeGzTransform_analyticAt {s : ℂ} (hs : s ≠ 0) (hz : riemannZeta s ≠ 0) :
    AnalyticAt ℂ alpogeNativeGzTransform s := by
  have hU : IsOpen {z : ℂ | riemannZeta₁ z ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have hD : DifferentiableOn ℂ (logDeriv riemannZeta₁) {z | riemannZeta₁ z ≠ 0} := by
    intro z hz'
    exact ((differentiable_riemannZeta₁.deriv z).div (differentiable_riemannZeta₁ z) hz').differentiableWithinAt
  have h1 : {z : ℂ | riemannZeta₁ z ≠ 0} ∈ 𝓝 1 := hU.mem_nhds (by simp)
  have h := ((differentiableOn_dslope h1).2 hD).analyticAt (hU.mem_nhds ((zeta₁_ne_zero_iff s).2 hz))
  exact (analyticAt_const.sub h).div analyticAt_id hs

private theorem zeta₁_not_locally_zero (z : ℂ) : ¬ ∀ᶠ s in 𝓝 z, riemannZeta₁ s = 0 := by
  intro h
  have ha : AnalyticOnNhd ℂ riemannZeta₁ univ := fun w _ => differentiable_riemannZeta₁.analyticAt w
  have hzero := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h
  simpa using hzero (mem_univ 1)

private theorem logDeriv_zero_expansion {ρ : ℂ} (hz : riemannZeta₁ ρ = 0) :
    ∃ m : ℕ, m = analyticOrderNatAt riemannZeta₁ ρ ∧ 0 < m ∧ ∃ a : ℂ → ℂ, AnalyticAt ℂ a ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, logDeriv riemannZeta₁ s = (m : ℂ) / (s - ρ) + a s := by
  have ha := differentiable_riemannZeta₁.analyticAt ρ
  have hfin : analyticOrderAt riemannZeta₁ ρ ≠ ⊤ :=
    fun h => zeta₁_not_locally_zero ρ (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, heq⟩ := ha.analyticOrderAt_ne_top.mp hfin
  let m := analyticOrderNatAt riemannZeta₁ ρ
  have hm : m ≠ 0 := by
    intro h
    have : analyticOrderAt riemannZeta₁ ρ = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfin]
      change (m : ℕ∞) = 0
      simp [h]
    exact (ha.analyticOrderAt_eq_zero.mp this) hz
  refine ⟨m, rfl, Nat.pos_of_ne_zero hm, logDeriv g, hg.deriv.div hg hg0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds heq.eventually_nhds,
      nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0),
      nhdsWithin_le_nhds hg.eventually_analyticAt, self_mem_nhdsWithin] with s hs hgs hag hsρ
  have he : riemannZeta₁ =ᶠ[𝓝 s] (fun z => (z - ρ) ^ m * g z) := hs
  have hp : HasDerivAt (fun z => (z - ρ) ^ m * g z)
      (m * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
    (((hasDerivAt_id' s).sub_const ρ).pow m).mul hag.differentiableAt.hasDerivAt
  rw [logDeriv_apply, he.deriv_eq, hp.deriv, he.self_of_nhds, logDeriv_apply]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
  simp only [hk, Nat.succ_sub_one, pow_succ, mul_one]
  field_simp [sub_ne_zero.mpr (show s ≠ ρ from hsρ), hgs]

theorem alpogeNativeGzTransform_at_zero {ρ : ℂ} (hρ : 0 < ρ.re) (hz : riemannZeta ρ = 0) :
    ∃ m : ℕ, m = analyticOrderNatAt riemannZeta ρ ∧ 0 < m ∧ ∃ a : ℂ → ℂ, AnalyticAt ℂ a ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, alpogeNativeGzTransform s = (-(m : ℂ) / (ρ * (ρ - 1))) / (s - ρ) + a s := by
  have h0 := Complex.ne_zero_of_re_pos hρ
  have h1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  have hz₁ : riemannZeta₁ ρ = 0 := not_ne_iff.mp (fun h => (zeta₁_ne_zero_iff ρ).1 h hz)
  obtain ⟨m, horder, hm, a, ha, hpart⟩ := logDeriv_zero_expansion hz₁
  have heq : riemannZeta₁ =ᶠ[𝓝 ρ] (fun s : ℂ => s - 1) * riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds h1] with s hs
    simp [riemannZeta_eq_inv_sub_mul hs, sub_ne_zero.mpr hs]
  have hunit : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := by fun_prop
  have hmζ : m = analyticOrderNatAt riemannZeta ρ := by
    rw [horder, analyticOrderNatAt, analyticOrderAt_congr heq,
      analyticOrderAt_mul hunit (differentiableOn_riemannZeta.analyticAt (isOpen_ne.mem_nhds h1)),
      hunit.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h1), zero_add]
    rfl
  let K : ℂ → ℂ := fun s => 1 / (s * (s - 1))
  have hK : AnalyticAt ℂ K ρ := analyticAt_const.div
    (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  have hd : AnalyticAt ℂ (dslope K ρ) ρ := by
    obtain ⟨p, hp⟩ := hK
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  refine ⟨m, hmζ, hm, fun s => (1 + (γ₀ : ℂ)) / s - (a s - γ₀) * K s - (m : ℂ) * dslope K ρ s,
    ((analyticAt_const.div analyticAt_id h0).sub ((ha.sub analyticAt_const).mul hK)).sub
      (analyticAt_const.mul hd), ?_⟩
  filter_upwards [hpart, self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ne.mem_nhds h1),
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)] with s hpart hsρ hs1 hs0
  rw [transform_off_one hs1, hpart, dslope_of_ne _ (show s ≠ ρ from hsρ), slope_def_field]
  dsimp [K]
  field_simp [hs0, h0, sub_ne_zero.mpr hs1, sub_ne_zero.mpr h1, sub_ne_zero.mpr (show s ≠ ρ from hsρ)]
  ring

private theorem gz_growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    |alpogeNativeGzArithmetic (Real.exp u)| ≤ C * Real.exp (2 * u) := by
  let B := Real.log 4 + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * B + |1 + γ₀| + 2, fun u hu => ?_⟩
  let x := Real.exp u
  have hx : 1 ≤ x := Real.one_le_exp hu
  have hx0 : 0 ≤ x := by linarith
  have hfloor := Nat.floor_le hx0
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hrecip : nativeLambdaRecip ⌊x⌋₊ ≤ x + B := by
    have hlogN := Real.log_le_log (by exact_mod_cast hn : 0 < (⌊x⌋₊ : ℝ)) hfloor
    linarith [(nativeLambdaRecip_sub_log_bounds ⌊x⌋₊ hn).2]
  have hrecip0 : 0 ≤ nativeLambdaRecip ⌊x⌋₊ := by
    unfold nativeLambdaRecip
    exact Finset.sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hψ := (nativePsi_le_const_mul ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left hfloor hB)
  change nativePsi _ ≤ B * x at hψ
  have hψ0 := nativePsi_nonneg ⌊x⌋₊
  have hsq : x ≤ x ^ 2 := by nlinarith
  rw [two_mul u, Real.exp_add]
  change |x * nativeLambdaRecip ⌊x⌋₊ - nativePsi ⌊x⌋₊ - x * Real.log x + (1 + γ₀) * x| ≤ (2 * B + |1 + γ₀| + 2) * (x * x)
  rw [abs_le]
  constructor <;> nlinarith only [hsq, mul_nonneg hx0 hrecip0, mul_le_mul_of_nonneg_left hrecip hx0,
    hψ, hψ0, mul_nonneg hx0 (Real.log_nonneg hx), mul_le_mul_of_nonneg_left hlog hx0,
    mul_le_mul_of_nonneg_right (neg_abs_le (1 + γ₀)) hx0,
    mul_le_mul_of_nonneg_right (le_abs_self (1 + γ₀)) hx0,
    mul_nonneg hB hx0, mul_nonneg (abs_nonneg (1 + γ₀)) hx0,
    mul_le_mul_of_nonneg_left hsq hB, mul_le_mul_of_nonneg_left hsq (abs_nonneg (1 + γ₀)), hx0]

theorem alpogeNativeGzArithmetic_poleData :
    WindowLandau.PoleData (fun u => alpogeNativeGzArithmetic (Real.exp u))
      alpogeNativeGzTransform {s : ℂ | 0 < s.re ∧ riemannZeta s = 0} := by
  constructor
  · have hfloor := Real.measurable_exp.nat_floor
    unfold alpogeNativeGzArithmetic
    exact (((Real.measurable_exp.mul ((measurable_from_nat (f := nativeLambdaRecip)).comp hfloor)).sub
      ((measurable_from_nat (f := nativePsi)).comp hfloor)).sub
      (Real.measurable_exp.mul (Real.measurable_log.comp Real.measurable_exp))).add
      (measurable_const.mul Real.measurable_exp)
  · exact gz_growth
  · exact fun s hs => alpogeNativeGzTransform_laplace (by linarith)
  · intro ρ hρ
    exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρ.2)
  · intro s hs
    exact (alpogeNativeGzTransform_analyticAt (Complex.ne_zero_of_re_pos hs.1)
      (fun hz => hs.2 ⟨hs.1, hz⟩)).differentiableAt.differentiableWithinAt
  · intro z _
    have h := (differentiable_riemannZeta₁.analyticAt z).eventually_eq_zero_or_eventually_ne_zero
    filter_upwards [h.resolve_left (zeta₁_not_locally_zero z)] with w hw
    exact fun hz => (zeta₁_ne_zero_iff w).1 hw hz.2
  · intro ρ hρ
    obtain ⟨m, -, hm, a, ha, hpart⟩ := alpogeNativeGzTransform_at_zero hρ.1 hρ.2
    have hlt : ρ.re < 1 := lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hρ.2)
    have h0 := Complex.ne_zero_of_re_pos hρ.1
    have h1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hρ.2
    refine ⟨-(m : ℂ) / (ρ * (ρ - 1)), div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hm.ne'))
      (mul_ne_zero h0 (sub_ne_zero.mpr h1)), ?_, a, ha, hpart⟩
    intro him
    have hre : (ρ.re : ℂ) = ρ := Complex.ext rfl (by simpa using him.symm)
    have hc : -(m : ℂ) / (ρ * (ρ - 1)) = ((-(m : ℝ) / (ρ.re * (ρ.re - 1)) : ℝ) : ℂ) := by
      push_cast
      rw [hre]
    rw [hc]
    exact ⟨div_pos_of_neg_of_neg (by exact neg_lt_zero.mpr (Nat.cast_pos.mpr hm))
      (mul_neg_of_pos_of_neg hρ.1 (sub_neg.mpr hlt)), rfl⟩

theorem riemannZeta_ne_zero_of_Gz_window {θ δ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), alpogeNativeGzArithmetic y ≤ C * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 := by
  have hw (U₀ : ℝ) : ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      alpogeNativeGzArithmetic (Real.exp u) ≤ |C| * Real.exp (θ * u) := by
    obtain ⟨Y, hY, hy⟩ := h (Real.exp U₀)
    have hpos := (Real.exp_pos U₀).trans_le hY
    refine ⟨Real.log Y, (Real.le_log_iff_exp_le hpos).2 hY, fun u hu => ?_⟩
    have hm : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← Real.exp_log hpos, ← Real.exp_mul]
      exact ⟨Real.exp_le_exp.mpr hu.1, Real.exp_le_exp.mpr (by simpa [mul_comm] using hu.2)⟩
    refine (hy _ hm).trans ?_
    rw [← Real.exp_mul, mul_comm θ u]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  intro s hs hz
  exact hs.not_ge (WindowLandau.landau_window alpogeNativeGzArithmetic_poleData hθ hθ1 hδ
    (abs_nonneg C) hw s ⟨hθ.trans hs, hz⟩)

theorem riemannHypothesis_of_Gz_windows {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), alpogeNativeGzArithmetic y ≤ C * y ^ (1 / 2 + η)) :
    RiemannHypothesis := by
  have hright (s : ℂ) (hs : 1 / 2 < s.re) : riemannZeta s ≠ 0 := by
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1
    let η := (s.re - 1 / 2) / 2
    obtain ⟨C, hw⟩ := h η (by dsimp [η]; linarith)
    apply riemannZeta_ne_zero_of_Gz_window (θ := 1 / 2 + η) (C := C) _ _ hδ hw s <;>
      dsimp [η] <;> linarith
  intro s hz htriv hs1
  apply le_antisymm (le_of_not_gt fun hs => hright s hs hz)
  by_contra! hleft
  have hs0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have hΓ : Gammaℝ s ≠ 0 := by
    rintro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    cases n with
    | zero => exact hs0 (by simpa using! hn)
    | succ k => exact htriv ⟨k, by simpa [Nat.cast_succ] using! hn⟩
  have hcomp : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hΓ
  apply hright (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hs1.symm), completedRiemannZeta_one_sub, hcomp, zero_div]

@[simp] theorem alpogeNativeGzArithmetic_natCast (N : ℕ) :
    alpogeNativeGzArithmetic (N : ℝ) = nativeAlpogeGz N := by
  simp [alpogeNativeGzArithmetic, nativeAlpogeGz]

theorem alpogeNativeGzArithmetic_le_floor (y : ℝ) (hy : 1 ≤ y) :
    alpogeNativeGzArithmetic y ≤ nativeAlpogeGz ⌊y⌋₊ + nativeAlpogeSafeSlope * (y - ⌊y⌋₊) := by
  let n := ⌊y⌋₊
  have hn : 1 ≤ n := (Nat.le_floor_iff (by linarith : 0 ≤ y)).mpr (by simpa using hy)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < y := by linarith
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0.le
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hy0)
  rw [Real.log_div hn0.ne' hy0.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hy0.le
  have heq : ((n : ℝ) / y - 1) * y = n - y := by field_simp
  rw [heq] at hmul
  have hM := (nativeLambdaRecip_sub_log_bounds n hn).2
  have hslope : nativeLambdaRecip n - Real.log n + γ₀ ≤ nativeAlpogeSafeSlope := by
    unfold nativeAlpogeSafeSlope
    linarith [le_abs_self γ₀]
  have hbound := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hny)
  unfold alpogeNativeGzArithmetic nativeAlpogeGz
  change y * nativeLambdaRecip n - nativePsi n - y * Real.log y + (1 + γ₀) * y ≤
    n * nativeLambdaRecip n - nativePsi n - n * Real.log n + (1 + γ₀) * n + _
  nlinarith only [hmul, hbound]

/-- A root window from `A` to `A^(1+δ)` gives the real window starting at
`A²-1` with the same exponent. -/
theorem riemannHypothesis_of_squareClock_Gz_windows {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ A₀ : ℕ, ∃ A : ℕ, A₀ ≤ A ∧
      ∀ R : ℕ, A ≤ R → (R : ℝ) ≤ (A : ℝ) ^ (1 + δ) →
        nativeAlpogeGz (R ^ 2 - 1) ≤ C * ((R ^ 2 - 1 : ℕ) : ℝ) ^ (1 / 2 + η)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_Gz_windows hδ
  intro η hη
  obtain ⟨C, hw⟩ := h η hη
  refine ⟨|C| + 6 * nativeAlpogeSafeSlope, fun Y₀ => ?_⟩
  obtain ⟨A, hA, hanchors⟩ := hw (max 3 ⌈Y₀⌉₊)
  have hA3 : 3 ≤ A := (le_max_left _ _).trans hA
  have ha : (3 : ℝ) ≤ A := by exact_mod_cast hA3
  let Y : ℝ := (A : ℝ) ^ 2 - 1
  have hY₀ : Y₀ ≤ Y := by
    have hceil : ⌈Y₀⌉₊ ≤ A := (le_max_right _ _).trans hA
    have hYA := (Nat.le_ceil Y₀).trans (show (⌈Y₀⌉₊ : ℝ) ≤ A by exact_mod_cast hceil)
    dsimp [Y]
    nlinarith
  refine ⟨Y, hY₀, fun y hy => ?_⟩
  have hy4 : 4 ≤ y := by have := hy.1; dsimp [Y] at this; nlinarith
  have hy0 : 0 ≤ y := by linarith
  let N := ⌊y⌋₊
  let R := Nat.sqrt (N + 1)
  have hN : 4 ≤ N := (Nat.le_floor_iff hy0).mpr (by exact_mod_cast hy4)
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0
  have hR2 : R ^ 2 ≤ N + 1 := Nat.sqrt_le' _
  have hR2' : (R : ℝ) ^ 2 ≤ N + 1 := by exact_mod_cast hR2
  have hAR : A ≤ R := by
    apply Nat.le_sqrt'.2
    have hsq : (A : ℝ) ^ 2 - 1 ≤ y := hy.1
    have hfloor : A ^ 2 - 1 ≤ N := (Nat.le_floor_iff hy0).mpr (by
      rw [Nat.cast_sub (by nlinarith : 1 ≤ A ^ 2), Nat.cast_pow, Nat.cast_one]
      exact hsq)
    omega
  have hRhi : (R : ℝ) ≤ (A : ℝ) ^ (1 + δ) := by
    have hsup := Real.add_rpow_le_rpow_add (p := 1 + δ)
      (by dsimp [Y]; nlinarith : 0 ≤ Y) zero_le_one (by linarith)
    rw [Real.one_rpow, show Y + 1 = (A : ℝ) ^ 2 by dsimp [Y]; ring,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg A), mul_comm ((2 : ℕ) : ℝ) (1 + δ),
      Real.rpow_mul_natCast (Nat.cast_nonneg A) _ 2] at hsup
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg A) (1 + δ)
    nlinarith [hy.2]
  have hanchor : R ^ 2 - 1 ≤ N := by omega
  have haxy : ((R ^ 2 - 1 : ℕ) : ℝ) ≤ y := (Nat.cast_le.mpr hanchor).trans hNy
  let t : ℝ := 1 / 2 + η
  let upper := (A : ℝ) ^ (1 + δ)
  have hupper : 0 ≤ upper := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsample := nativeAlpogeGz_window_of_squareClock_window
    (fun r => C * ((r ^ 2 - 1 : ℕ) : ℝ) ^ t) A ⌊upper⌋₊ (by omega)
    (fun r hr hhi => hanchors r hr ((Nat.le_floor_iff hupper).mp hhi))
    N hN hAR ((Nat.le_floor_iff hupper).mpr hRhi)
  change nativeAlpogeGz N ≤ C * ((R ^ 2 - 1 : ℕ) : ℝ) ^ t +
    nativeAlpogeSafeSlope * ((2 * R + 1 : ℕ) : ℝ) at hsample
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hsample
  have hmain : C * ((R ^ 2 - 1 : ℕ) : ℝ) ^ t ≤ |C| * y ^ t :=
    mul_le_mul (le_abs_self _) (Real.rpow_le_rpow (by positivity) haxy (by dsimp [t]; linarith))
      (Real.rpow_nonneg (by positivity) _) (abs_nonneg C)
  have hsqrt := Real.sq_sqrt hy0
  have hy1 : 1 ≤ Real.sqrt y := by nlinarith [Real.sqrt_nonneg y]
  have hr : (R : ℝ) ≤ 2 * Real.sqrt y := by nlinarith [Real.sqrt_nonneg y]
  have hpow : Real.sqrt y ≤ y ^ t := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp [t]; linarith)
  have hfloor := Nat.lt_floor_add_one y
  have hreal := alpogeNativeGzArithmetic_le_floor y (by linarith)
  change alpogeNativeGzArithmetic y ≤ nativeAlpogeGz N + nativeAlpogeSafeSlope * (y - N) at hreal
  have hgap : y - (N : ℝ) + (2 * R + 1) ≤ 6 * y ^ t := by
    change y < (N : ℝ) + 1 at hfloor
    linarith
  change _ ≤ (|C| + 6 * nativeAlpogeSafeSlope) * y ^ t
  nlinarith only [hmain, hreal, hsample, mul_le_mul_of_nonneg_left hgap nativeAlpogeSafeSlope_nonneg]

end RHLean.Analysis
