import Mathlib

/-!
# A one-sided Landau theorem on logarithmic windows

The argument follows Levent Alpöge's `DedekindLFunctions/LandauTheorems`.
The gamma-kernel tail estimate localizes high Laplace derivatives to the window.
The real derivative compensates the negative part of the source when estimating
the derivative at a complex point. A nearest simple pole contradicts this joint
bound. All measures are real Lebesgue measure.

The analytic pole-exclusion step is also exposed directly for cofinally many
Laplace coefficients and for weighted positive first moments of the complete
signed source. These consumers keep their quantitative moment bound explicit;
the original logarithmic-window theorem and its hypotheses are preserved.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace RHLean.Analysis.WindowLandau

structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) : Prop where
  meas : Measurable g
  growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)
  laplace : ∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u)
  right : ∀ ρ ∈ Z, ρ.re < 1
  diff : DifferentiableOn ℂ Φ ({s : ℂ | 0 < s.re} \ Z)
  iso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s

/-- The weighted positive first moment of the complete signed source.
The order `k` belongs to the Laplace kernel; the positive part is taken only
after the entire value `g u` has been formed. -/
def weightedPositiveMoment (g : ℝ → ℝ) (σ : ℝ) (k : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), max (g u) 0 *
    (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))

private theorem kernel_integral (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) = (a ^ (k + 1))⁻¹ := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hk ha
  have e : ∀ u : ℝ, u ^ k * Real.exp (-a * u) = u ^ (((k : ℝ) + 1) - 1) * Real.exp (-(a * u)) :=
    fun u => by rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
  rw [MeasureTheory.integral_div]
  simp_rw [e]
  rw [key, Real.Gamma_nat_eq_factorial]
  have h2 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [h2, Real.rpow_natCast, one_div, inv_pow, mul_div_assoc, div_self hf, mul_one]

private theorem landau_tails_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by
  by_contra h
  have h1 := kernel_integral k a ha
  rw [integral_undef h] at h1
  have : 0 < (a ^ (k + 1))⁻¹ := by positivity
  linarith

private theorem landau_tails_chernoff (k : ℕ) {s l U V : ℝ} (hl : 0 ≤ l) (hs : l < s) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ) ≤
      Real.exp (-(l * V)) * ((s - l) ^ (k + 1))⁻¹ + Real.exp (l * U) * ((s + l) ^ (k + 1))⁻¹ := by
  have ha : 0 < s - l := by linarith
  have hb : 0 < s + l := by linarith
  have hs0 : 0 < s := by linarith
  have i1 := (landau_tails_integrable k ha).const_mul (Real.exp (-(l * V)))
  have i2 := (landau_tails_integrable k hb).const_mul (Real.exp (l * U))
  have i0 := landau_tails_integrable k hs0
  have i3 := i1.add i2
  rw [← kernel_integral k _ ha, ← kernel_integral k _ hb, ← integral_const_mul, ← integral_const_mul,
    ← integral_add i1 i2]
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  refine le_trans (setIntegral_mono_on (IntegrableOn.mono_set i0 sdiff_subset)
    (IntegrableOn.mono_set i3 sdiff_subset) hm ?_) (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)
  · intro u hu
    have hu0 : 0 < u := hu.1
    have hf : 0 < (k.factorial : ℝ) := by positivity
    have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
    have e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u)) := by
      have hn := hu.2
      rw [mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (U - u)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (u - V))]
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (U - u))]
    rw [← e1, ← e2] at key
    have := mul_le_mul_of_nonneg_left key hp
    simp only [Pi.add_apply]
    calc _ = u ^ k / (k.factorial : ℝ) * Real.exp (-s * u) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    simp only [Pi.add_apply, Pi.zero_apply]
    positivity

private theorem landau_tails_pow (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc _ ≤ Real.exp x * Real.exp (k * ((σ - a) / a)) := by gcongr
      _ = Real.exp (x + k * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 h
  calc _ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by
        rw [div_pow, pow_succ]; field_simp
    _ ≤ _ := by gcongr

private theorem landau_tails {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) ≤ C / σ ^ k := by
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℝ, 2 < l ∧ l * δ = 6 + 2 * δ := by
    refine ⟨2 + 6 / δ, by have : 0 < 6 / δ := by positivity
                          linarith, by field_simp; ring⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = l * (1 + δ) := ⟨_, rfl⟩
  have hMl : l < M := by nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = M * (2 + l) := ⟨_, rfl⟩
  have hσ1 : l * (2 + l) < σ := by rw [hσ]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  have hk1 := Nat.le_ceil ((1 + δ / 2) * σ * U)
  have hk2 := (Nat.ceil_lt_add_one hx).le
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hσU : 0 ≤ σ * U := by positivity
  refine ⟨k, ?_, ?_⟩
  · nlinarith [mul_nonneg hδ.le hσU]
  · have e : (2 - σ) = -(σ - 2) := by ring
    rw [e, add_div]
    refine (landau_tails_chernoff k (by linarith : 0 ≤ l) hs).trans (add_le_add ?_ ?_)
    · apply landau_tails_pow k hσ0 ha
      have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
        have : 0 < M - 1 := by linarith
        rw [div_eq_div_iff ha.ne' this.ne', hσ]; ring
      have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
        have : (1 + δ / 2) * (2 + l) = M - 1 := by rw [hM]; nlinarith
        rw [hσ, ← this]; ring
      have hM1 : 1 ≤ M - 1 := by linarith
      have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        rw [e2] at hk2
        nlinarith
      have e4 : l * ((1 + δ) * U) = M * U := by rw [hM]; ring
      rw [e1, e4]; linarith
    · apply landau_tails_pow k hσ0 hb
      have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by
        ring
      have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
      have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
        rw [le_div_iff₀ hb]
        have h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2) :=
          mul_le_mul_of_nonneg_right hk1 (by linarith)
        have h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
        have h3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
        have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)
        nlinarith
      rw [e1]; linarith

private theorem iteratedDeriv_laplace_int (n : ℕ) (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-b * u)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := b)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hb
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

private theorem iteratedDeriv_laplace_meas (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
  apply Measurable.aestronglyMeasurable
  fun_prop

private theorem iteratedDeriv_laplace_bound (g : ℝ → ℝ) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (b : ℝ) (z : ℂ) (hz : 2 + b ≤ z.re)
    (u : ℝ) (hu : 0 < u) :
    ‖(g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u)‖ ≤ C * (u ^ k * Real.exp (-b * u)) := by
  have h1 : ‖(g u : ℂ)‖ ≤ C * Real.exp (2 * u) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgC u hu.le
  have h2 : ‖((-u : ℝ) : ℂ) ^ k‖ = u ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hu]
  have h3 : ‖cexp (-z * u)‖ ≤ Real.exp (-(2 + b) * u) := by
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_im, mul_zero, sub_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hC : 0 ≤ C * Real.exp (2 * u) := le_trans (norm_nonneg _) h1
  rw [norm_mul, norm_mul, h2]
  calc ‖(g u : ℂ)‖ * u ^ k * ‖cexp (-z * u)‖
      ≤ C * Real.exp (2 * u) * u ^ k * Real.exp (-(2 + b) * u) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (norm_nonneg _)
          (mul_nonneg hC (by positivity))
    _ = C * (u ^ k * (Real.exp (2 * u) * Real.exp (-(2 + b) * u))) := by ring
    _ = C * (u ^ k * Real.exp (-b * u)) := by
        rw [← Real.exp_add]
        ring_nf

private theorem iteratedDeriv_laplace_hasDerivAt (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ)
    (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)) (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    HasDerivAt (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
      (∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-s * u)) s := by
  set δ := (s.re - 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hre : ∀ z ∈ Metric.ball s δ, 2 + δ ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h1
    have h2 := (abs_le.mp (h1.trans hz.le)).1
    linarith
  have hint : Integrable (fun u : ℝ => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u))
      (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' (Integrable.const_mul (iteratedDeriv_laplace_int k δ hδpos) C)
      (iteratedDeriv_laplace_meas g hg k s) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact iteratedDeriv_laplace_bound g C hgC k δ s (hre s (Metric.mem_ball_self hδpos)) u hu
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-z * u))
    (F' := fun z u => (g u : ℂ) * ((-u : ℝ) : ℂ) ^ (k + 1) * cexp (-z * u))
    (Metric.ball_mem_nhds s hδpos)
    (Eventually.of_forall fun z => iteratedDeriv_laplace_meas g hg k z) hint
    (iteratedDeriv_laplace_meas g hg (k + 1) s) ?_
    (Integrable.const_mul (iteratedDeriv_laplace_int (k + 1) δ hδpos) C) ?_).2
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu z hz => ?_)
    exact iteratedDeriv_laplace_bound g C hgC (k + 1) δ z (hre z hz) u hu
  · refine Eventually.of_forall fun u z _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z := by
      simpa using (hasDerivAt_id' z).neg.mul_const (u : ℂ)
    have h2 := h1.cexp.const_mul ((g u : ℂ) * ((-u : ℝ) : ℂ) ^ k)
    refine h2.congr_deriv ?_
    push_cast
    ring

private theorem iteratedDeriv_laplace (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hgC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (k : ℕ) (s : ℂ) (hs : 2 < s.re) :
    iteratedDeriv k (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) s =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ k * cexp (-s * u) := by
  have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ j : ℕ, ∀ z : ℂ, 2 < z.re →
      iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) z =
        ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-z * u) := by
    intro j
    induction j with
    | zero =>
      intro z _
      simp
    | succ j ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u))
          =ᶠ[𝓝 z] fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * ((-u : ℝ) : ℂ) ^ j * cexp (-w * u) :=
        Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => ih w hw
      rw [hev.deriv_eq]
      exact (iteratedDeriv_laplace_hasDerivAt g hg C hgC j z hz).deriv
  exact key k s hs

private theorem landau_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by
  obtain ⟨C, hC⟩ := hP.growth
  have hev : Φ =ᶠ[𝓝 s] (fun z => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hP.laplace z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_laplace g hP.meas C hC k s hs, ← integral_const_mul,
    ← integral_div]
  congr 1
  funext u
  push_cast
  have e : ((-1 : ℂ)) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]
    ring
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * (-(u : ℂ)) ^ k * cexp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * cexp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by rw [e]

private theorem landau_weighted_integrable {g : ℝ → ℝ} (hg : Measurable g) {C₀ σ : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u))
    (hσ : 2 < σ) (k : ℕ) :
    IntegrableOn (fun u : ℝ => |g u| *
      (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ => g u *
      (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))) (Ioi 0) ∧
    IntegrableOn (fun u : ℝ => max (g u) 0 *
      (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))) (Ioi 0) := by
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ) with hw
  set t : ℝ → ℝ := fun u => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) with ht
  have hti : IntegrableOn t (Ioi 0) := by
    simpa only [ht, neg_sub] using landau_tails_integrable k (show 0 < σ - 2 by linarith)
  have hw0 : ∀ u, 0 ≤ u → 0 ≤ w u := fun u hu => by simp only [hw]; positivity
  have hwm : Measurable w := by simp only [hw]; fun_prop
  have hb : ∀ u, 0 ≤ u → |g u| * w u ≤ C₀ * t u := fun u hu => by
    have he : C₀ * t u = C₀ * Real.exp (2 * u) * w u := by
      simp only [hw, ht]
      rw [show (2 - σ) * u = 2 * u + -σ * u by ring, Real.exp_add]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (hC u hu) (hw0 u hu)
  have hI1 : IntegrableOn (fun u => |g u| * w u) (Ioi 0) := by
    refine Integrable.mono' (hti.const_mul C₀) (hg.abs.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hw0 u hu.le))]
    exact hb u hu.le
  have hI2 : IntegrableOn (fun u => g u * w u) (Ioi 0) := by
    refine Integrable.mono' (hti.const_mul C₀) (hg.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hw0 u hu.le), Real.norm_eq_abs]
    exact hb u hu.le
  refine ⟨hI1, hI2, ?_⟩
  refine Integrable.mono' hI1 ((hg.max measurable_const).mul hwm).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (hw0 u hu.le))]
  exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (hw0 u hu.le)

/-- The positive moment is an integrable first moment for every order at
every permitted Laplace line. Its value is not an undefined-integral zero. -/
theorem weightedPositiveMoment_integrable {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {σ : ℝ} (hσ : 2 < σ) (k : ℕ) :
    IntegrableOn (fun u : ℝ => max (g u) 0 *
      (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ))) (Ioi 0) := by
  obtain ⟨C₀, hC₀⟩ := hP.growth
  exact (landau_weighted_integrable hP.meas hC₀ hσ k).2.2

theorem weightedPositiveMoment_nonneg (g : ℝ → ℝ) (σ : ℝ) (k : ℕ) :
    0 ≤ weightedPositiveMoment g σ k := by
  unfold weightedPositiveMoment
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  have hu0 : 0 ≤ u := hu.le
  exact mul_nonneg (le_max_right _ _) (by positivity)

/-- A supplied exponential upper bound gives its exact gamma-kernel moment
bound. This does not require an absolute bound at that same exponent. -/
theorem weightedPositiveMoment_le_of_exp_upper
    {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {σ α B : ℝ} (hσ : 2 < σ) (hα : α < σ) (hB : 0 ≤ B)
    (hupper : ∀ u : ℝ, 0 ≤ u → g u ≤ B * Real.exp (α * u)) (k : ℕ) :
    weightedPositiveMoment g σ k ≤ B / (σ - α) ^ (k + 1) := by
  have hi : IntegrableOn (fun u : ℝ =>
      B * (u ^ k * Real.exp (-(σ - α) * u) / (k.factorial : ℝ))) (Ioi 0) :=
    (landau_tails_integrable k (sub_pos.mpr hα)).const_mul B
  calc
    weightedPositiveMoment g σ k ≤ ∫ u in Ioi (0 : ℝ),
        B * (u ^ k * Real.exp (-(σ - α) * u) / (k.factorial : ℝ)) := by
      unfold weightedPositiveMoment
      refine setIntegral_mono_on (weightedPositiveMoment_integrable hP hσ k) hi
        measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 ≤ u := hu.le
      have hpos : 0 ≤ B * Real.exp (α * u) := by positivity
      have hmajor : max (g u) 0 ≤ B * Real.exp (α * u) :=
        max_le (hupper u hu0) hpos
      calc
        _ ≤ (B * Real.exp (α * u)) *
            (u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hmajor (by positivity)
        _ = _ := by
          rw [show -(σ - α) * u = α * u + -σ * u by ring, Real.exp_add]
          ring
    _ = B * ((σ - α) ^ (k + 1))⁻¹ := by
      rw [integral_const_mul, kernel_integral k (σ - α) (sub_pos.mpr hα)]
    _ = B / (σ - α) ^ (k + 1) := by rw [div_eq_mul_inv]

private theorem weightedPositiveMoment_window_le {g : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hg : Measurable g) {C₀ : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u))
    {σ θ U V : ℝ} (hσ : 2 < σ) (hθ : θ < σ) (hU : 0 < U)
    (hR : ∀ u ∈ Icc U V, g u ≤ B * Real.exp (θ * u)) (k : ℕ) :
    weightedPositiveMoment g σ k ≤ B * ((σ - θ) ^ (k + 1))⁻¹ +
      C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V,
        u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) := by
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ) with hw
  set t : ℝ → ℝ := fun u => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) with ht
  have hti : IntegrableOn t (Ioi 0) := by
    simpa only [ht, neg_sub] using landau_tails_integrable k (show 0 < σ - 2 by linarith)
  have hw0 : ∀ u, 0 ≤ u → 0 ≤ w u := fun u hu => by simp only [hw]; positivity
  have hI : IntegrableOn (fun u => max (g u) 0 * w u) (Ioi 0) :=
    (landau_weighted_integrable hg hC hσ k).2.2
  have hb : ∀ u, 0 ≤ u → max (g u) 0 * w u ≤ C₀ * t u := fun u hu => by
    have he : C₀ * t u = C₀ * Real.exp (2 * u) * w u := by
      simp only [hw, ht]
      rw [show (2 - σ) * u = 2 * u + -σ * u by ring, Real.exp_add]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      ((max_le (le_abs_self _) (abs_nonneg _)).trans (hC u hu)) (hw0 u hu)
  have hsub : Icc U V ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le hU hu.1
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ))
    (t := Icc U V) measurableSet_Icc hI
  rw [inter_eq_right.2 hsub] at hsplit
  have hA : ∫ u in Icc U V, max (g u) 0 * w u ≤
      B * ((σ - θ) ^ (k + 1))⁻¹ := by
    let kernel := fun u : ℝ => u ^ k * Real.exp (-(σ - θ) * u) / (k.factorial : ℝ)
    have hi : IntegrableOn (fun u => B * kernel u) (Ioi 0) :=
      (landau_tails_integrable k (sub_pos.mpr hθ)).const_mul B
    rw [← kernel_integral k _ (sub_pos.mpr hθ), ← integral_const_mul]
    refine (setIntegral_mono_on (hI.mono_set hsub) (hi.mono_set hsub)
      measurableSet_Icc ?_).trans (setIntegral_mono_set hi ?_ hsub.eventuallyLE)
    · intro u hu
      have hpos : 0 ≤ B * Real.exp (θ * u) := by positivity
      have hmajor : max (g u) 0 ≤ B * Real.exp (θ * u) := max_le (hR u hu) hpos
      calc
        max (g u) 0 * w u ≤ (B * Real.exp (θ * u)) * w u :=
          mul_le_mul_of_nonneg_right hmajor (hw0 u (hsub hu).le)
        _ = B * kernel u := by
          dsimp [kernel, w]
          rw [show -(σ - θ) * u = θ * u + -σ * u by ring, Real.exp_add]
          ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 ≤ u := hu.le
      positivity
  have hT : ∫ u in Ioi (0 : ℝ) \ Icc U V, max (g u) 0 * w u ≤
      C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, t u := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hI.mono_set sdiff_subset)
      ((hti.mono_set sdiff_subset).const_mul C₀)
      (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => hb u hu.1.le
  change (∫ u in Ioi (0 : ℝ), max (g u) 0 * w u) ≤
    B * ((σ - θ) ^ (k + 1))⁻¹ + C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, t u
  linarith only [hsplit, hA, hT]

/-- The original one-sided windows imply the cofinal positive-moment
hypothesis. The window pays `B / (σ-θ)^(k+1)`; the original exponential
growth bound pays both tails. The Laplace line and constant are chosen
before the requested lower bound on the moment order. -/
theorem positiveMoment_bound_of_windows
    {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ δ B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀,
      ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ B * Real.exp (θ * u)) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k₀ : ℕ, ∃ k ≥ k₀,
      weightedPositiveMoment g σ k ≤ C / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, T, ht⟩ := landau_tails hδ
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀pos : 0 ≤ C₀ := (abs_nonneg _).trans (by simpa using hC₀ 0 le_rfl)
  have ha : 0 < σ - θ := by linarith
  refine ⟨σ, hσ, B / (σ - θ) + C₀ * |T|, by positivity, fun k₀ => ?_⟩
  obtain ⟨U, hU, hw⟩ := hW (max (k₀ : ℝ) 1)
  have hu : 1 ≤ U := (le_max_right _ _).trans hU
  obtain ⟨k, hk, htail⟩ := ht U hu
  refine ⟨k, by exact_mod_cast ((le_max_left _ _).trans hU).trans hk, ?_⟩
  have h := weightedPositiveMoment_window_le hB hP.meas hC₀ hσ
    (by linarith : θ < σ) (by linarith : 0 < U) hw k
  have hscale : T / σ ^ k ≤ |T| / (σ - θ) ^ k :=
    div_le_div₀ (abs_nonneg _) (le_abs_self _) (pow_pos ha _)
      (pow_le_pow_left₀ ha.le (by linarith) k)
  have hcost := mul_le_mul_of_nonneg_left (htail.trans hscale) hC₀pos
  rw [pow_succ, mul_inv] at h
  rw [add_div]
  simp only [div_eq_mul_inv] at h hcost ⊢
  linarith only [h, hcost]

/-- The real Laplace coefficient cancels the negative-source contribution
in the norm estimate. Only twice the completed positive moment is charged. -/
theorem landau_coefficients_le_positiveMoment
    {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {σ : ℝ} (hσ : 2 < σ) (k : ℕ) (γ : ℝ) :
    ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        2 * weightedPositiveMoment g σ k := by
  obtain ⟨C₀, hC₀⟩ := hP.growth
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ) with hw
  obtain ⟨hI1, hI2, _hI3⟩ := landau_weighted_integrable hP.meas hC₀ hσ k
  rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
    landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
  have hL : ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k *
      cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖ ≤
      ∫ u in Ioi (0 : ℝ), |g u| * w u := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := hu.le
    have hre : (-((σ : ℂ) + γ * I) * u).re = -σ * u := by simp
    simp only [hw, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, hre,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hu0]
    ring
  have hM : (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k *
      cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re =
      ∫ u in Ioi (0 : ℝ), g u * w u := by
    have he : (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ k *
        cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)) =
        fun u : ℝ => ((g u * w u : ℝ) : ℂ) := by
      funext u
      simp only [hw]
      push_cast
      ring
    rw [he, integral_complex_ofReal, Complex.ofReal_re]
  rw [hM]
  calc
    _ ≤ (∫ u in Ioi (0 : ℝ), |g u| * w u) +
        ∫ u in Ioi (0 : ℝ), g u * w u := add_le_add hL le_rfl
    _ = ∫ u in Ioi (0 : ℝ), (|g u| * w u + g u * w u) :=
      (integral_add hI1 hI2).symm
    _ = ∫ u in Ioi (0 : ℝ), 2 * (max (g u) 0 * w u) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _hu => ?_
      by_cases hgu : 0 ≤ g u
      · rw [abs_of_nonneg hgu, max_eq_left hgu]
        ring
      · have hgu' : g u ≤ 0 := le_of_not_ge hgu
        rw [abs_of_nonpos hgu', max_eq_right hgu']
        ring
    _ = 2 * weightedPositiveMoment g σ k := by
      rw [integral_const_mul]
      rfl

private theorem landau_window_ineq {g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hg : Measurable g) {C₀ : ℝ}
    (hC : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (2 * u)) {σ θ U V : ℝ} (hσ : 2 < σ) (hθ : θ < σ) (hU : 0 < U)
    (hR : ∀ u ∈ Icc U V, g u ≤ B * Real.exp (θ * u)) (k : ℕ) (γ : ℝ) :
    ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖ ≤
      2 * B * ((σ - θ) ^ (k + 1))⁻¹ -
        (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re +
        2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) := by
  set w : ℝ → ℝ := fun u => u ^ k * Real.exp (-σ * u) / (k.factorial : ℝ) with hw
  set h : ℝ → ℝ := fun u => u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) with hh
  have hhi : IntegrableOn h (Ioi 0) := by
    simpa only [hh, neg_sub] using landau_tails_integrable k (show 0 < σ - 2 by linarith)
  have hw0 : ∀ u, 0 ≤ u → 0 ≤ w u := fun u hu => by simp only [hw]; positivity
  have hwm : Measurable w := by simp only [hw]; fun_prop
  have hb : ∀ u, 0 ≤ u → |g u| * w u ≤ C₀ * h u := fun u hu => by
    have : C₀ * h u = C₀ * Real.exp (2 * u) * w u := by
      simp only [hw, hh]
      have : (2 - σ) * u = 2 * u + -σ * u := by ring
      rw [this, Real.exp_add]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (hC u hu) (hw0 u hu)
  have hI1 : IntegrableOn (fun u => |g u| * w u) (Ioi 0) := by
    refine Integrable.mono' (hhi.const_mul C₀) (hg.abs.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hw0 u (le_of_lt hu)))]
    exact hb u (le_of_lt hu)
  have hI2 : IntegrableOn (fun u => g u * w u) (Ioi 0) := by
    refine Integrable.mono' (hhi.const_mul C₀) (hg.mul hwm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hw0 u (le_of_lt hu)), Real.norm_eq_abs]
    exact hb u (le_of_lt hu)
  have hL : ‖∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-((σ : ℂ) + γ * I) * u) / (k.factorial : ℂ)‖
      ≤ ∫ u in Ioi (0 : ℝ), |g u| * w u := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu
    have hre : (-((σ : ℂ) + γ * I) * u).re = -σ * u := by simp
    simp only [hw, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, hre,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hu0]
    ring
  have hM : (∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ)).re
      = ∫ u in Ioi (0 : ℝ), g u * w u := by
    have : (fun u : ℝ => (g u : ℂ) * (u : ℂ) ^ k * cexp (-(σ : ℂ) * u) / (k.factorial : ℂ))
        = fun u : ℝ => ((g u * w u : ℝ) : ℂ) := by
      funext u
      simp only [hw]
      push_cast
      ring
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  have hI3 : IntegrableOn (fun u => |g u| * w u + g u * w u) (Ioi 0) := hI1.add hI2
  have hsub : Icc U V ⊆ Ioi (0 : ℝ) := fun u hu => lt_of_lt_of_le hU hu.1
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ)) (t := Icc U V)
    measurableSet_Icc hI3
  rw [inter_eq_right.2 hsub, integral_add hI1 hI2] at hsplit
  have hA : ∫ u in Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * B * ((σ - θ) ^ (k + 1))⁻¹ := by
    let kernel := fun u : ℝ => u ^ k * Real.exp (-(σ - θ) * u) / (k.factorial : ℝ)
    have hi : IntegrableOn (fun u => 2 * B * kernel u) (Ioi 0) :=
      (landau_tails_integrable k (sub_pos.mpr hθ)).const_mul (2 * B)
    rw [← kernel_integral k _ (sub_pos.mpr hθ), ← integral_const_mul]
    refine (setIntegral_mono_on (hI3.mono_set hsub) (hi.mono_set hsub) measurableSet_Icc ?_).trans
      (setIntegral_mono_set hi ?_ hsub.eventuallyLE)
    · intro u hu
      have hmajor := hR u hu
      have hpos : 0 ≤ B * Real.exp (θ * u) := by positivity
      have hplus : |g u| + g u ≤ 2 * (B * Real.exp (θ * u)) := by
        rcases abs_cases (g u) with h | h <;> linarith [h.1]
      calc |g u| * w u + g u * w u = (|g u| + g u) * w u := by ring
        _ ≤ 2 * (B * Real.exp (θ * u)) * w u :=
          mul_le_mul_of_nonneg_right hplus (hw0 u (hsub hu).le)
        _ = 2 * B * kernel u := by
          dsimp [kernel, w]
          rw [show -(σ - θ) * u = θ * u + -σ * u by ring, Real.exp_add]
          ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have : 0 ≤ u := le_of_lt hu
      positivity
  have hB : ∫ u in Ioi (0 : ℝ) \ Icc U V, (|g u| * w u + g u * w u)
      ≤ 2 * C₀ * ∫ u in Ioi (0 : ℝ) \ Icc U V, h u := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hI3.mono_set sdiff_subset) ((hhi.mono_set sdiff_subset).const_mul _)
      (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have h1 := hb u hu0
    have h2 : g u * w u ≤ |g u| * w u := mul_le_mul_of_nonneg_right (le_abs_self _) (hw0 u hu0)
    linarith
  rw [hM]
  linarith

private theorem landau_finite {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {z : ℂ} {r : ℝ}
    (hr : r < z.re) : (Z ∩ Metric.closedBall z r).Finite := by
  have hK : IsCompact (Metric.closedBall z r) := isCompact_closedBall z r
  have hpos : ∀ w ∈ Metric.closedBall z r, 0 < w.re := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h3 := (abs_le.mp (h2.trans h1)).1
    simp only [Complex.sub_re] at h3
    linarith
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => {v | v ∈ ({w}ᶜ : Set ℂ) → v ∉ Z})
    (fun w hw => eventually_nhdsWithin_iff.mp (hiso w (hpos w hw)))
  refine t.finite_toSet.subset ?_
  rintro v ⟨hvZ, hvK⟩
  obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.mp (ht hvK)
  by_cases h : v = w
  · rw [h]; exact hw
  · exact absurd hvZ (hvw h)

private theorem landau_nearest_equi {σ γ : ℝ} {a b : ℂ} (ha : a.re < σ) (hb : b.re < σ)
    (h : ‖(σ : ℂ) + γ * I - a‖ = ‖(σ : ℂ) + γ * I - b‖)
    (hγ : γ ≠ ((σ - a.re) ^ 2 + a.im ^ 2 - (σ - b.re) ^ 2 - b.im ^ 2) / (2 * (a.im - b.im))) :
    a = b := by
  have h2 : ‖(σ : ℂ) + γ * I - a‖ ^ 2 = ‖(σ : ℂ) + γ * I - b‖ ^ 2 := by rw [h]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im] at h2
  have him : a.im = b.im := by
    by_contra hne
    apply hγ
    have hne' : 2 * (a.im - b.im) ≠ 0 := by
      have := sub_ne_zero.mpr hne
      positivity
    rw [eq_div_iff hne']
    linear_combination -h2
  have hsq : (b.re - a.re) * ((σ - a.re) + (σ - b.re)) = 0 := by
    rw [him] at h2
    linear_combination h2
  rcases mul_eq_zero.mp hsq with h3 | h3
  · apply Complex.ext
    · linarith
    · exact him
  · exfalso
    linarith

private theorem landau_nearest {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ D : ℝ}
    (hle : ∀ ρ ∈ Z, ρ.re < σ) (hD : D < σ) {ρ₁ : ℂ} (h₁ : ρ₁ ∈ Z) (hρ₁ : σ - ρ₁.re < D) :
    ∃ γ : ℝ, ∃ ρ ∈ Z, ∃ r : ℝ, ‖(σ : ℂ) + γ * I - ρ‖ < r ∧ r ≤ D ∧
      ∀ w ∈ Z, w ∈ Metric.ball ((σ : ℂ) + γ * I) r → w = ρ := by
  obtain ⟨ε, hε0, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ (D - (σ - ρ₁.re)) / 2 ∧ ε ≤ (σ - D) / 2 := by
    refine ⟨min (D - (σ - ρ₁.re)) (σ - D) / 2, ?_, ?_, ?_⟩
    · have := lt_min (show 0 < D - (σ - ρ₁.re) by linarith) (show 0 < σ - D by linarith)
      linarith
    · have := min_le_left (D - (σ - ρ₁.re)) (σ - D)
      linarith
    · have := min_le_right (D - (σ - ρ₁.re)) (σ - D)
      linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, c₀ = (σ : ℂ) + ρ₁.im * I := ⟨_, rfl⟩
  have hc₀re : c₀.re = σ := by rw [hc₀]; simp
  have hF : (Z ∩ Metric.closedBall c₀ (D + ε)).Finite :=
    landau_finite hiso (by rw [hc₀re]; linarith)
  set F := Z ∩ Metric.closedBall c₀ (D + ε) with hFdef
  set B : Set ℝ := (fun p : ℂ × ℂ =>
      ((σ - p.1.re) ^ 2 + p.1.im ^ 2 - (σ - p.2.re) ^ 2 - p.2.im ^ 2) / (2 * (p.1.im - p.2.im))) ''
      (F ×ˢ F) with hB
  have hBfin : B.Finite := (hF.prod hF).image _
  obtain ⟨γ, hγI, hγB⟩ := ((Set.Ioo_infinite (show ρ₁.im - ε < ρ₁.im + ε by linarith)).sdiff hBfin).nonempty
  set c : ℂ := (σ : ℂ) + γ * I with hc
  have hγε : |γ - ρ₁.im| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hγI.2], by linarith [hγI.1]⟩
  have hcc₀ : ‖c - c₀‖ = |γ - ρ₁.im| := by
    have e : c - c₀ = ((γ - ρ₁.im : ℝ) : ℂ) * I := by
      rw [hc, hc₀]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hc₀ρ₁ : ‖c₀ - ρ₁‖ = σ - ρ₁.re := by
    have e : c₀ - ρ₁ = ((σ - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc₀]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hle ρ₁ h₁))]
  have hρ₁F : ρ₁ ∈ F := by
    refine ⟨h₁, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, hc₀ρ₁]
    linarith
  obtain ⟨ρ, hρF, hmin⟩ := Set.exists_min_image F (fun w => ‖c - w‖) hF ⟨ρ₁, hρ₁F⟩
  have hρ₁c : ‖c - ρ₁‖ < D := by
    have := norm_add_le (c - c₀) (c₀ - ρ₁)
    rw [sub_add_sub_cancel, hcc₀, hc₀ρ₁] at this
    linarith
  have hm : ‖c - ρ‖ ≤ ‖c - ρ₁‖ := hmin ρ₁ hρ₁F
  have hT : ∀ w ∈ F \ {ρ}, ‖c - ρ‖ < ‖c - w‖ := by
    intro w hw
    have hmw : ‖c - ρ‖ ≤ ‖c - w‖ := hmin w hw.1
    rcases lt_or_eq_of_le hmw with h | h
    · exact h
    · exfalso
      apply hw.2
      exact landau_nearest_equi (hle w hw.1.1) (hle ρ hρF.1) h.symm
        (fun hb => hγB ⟨(w, ρ), ⟨hw.1, hρF⟩, hb.symm⟩)
  obtain ⟨r, hr, hrT⟩ : ∃ r, ‖c - ρ‖ < r ∧ ∀ t ∈ F \ {ρ}, r ≤ ‖c - t‖ := by
    rcases (F \ {ρ}).eq_empty_or_nonempty with hTe | hTne
    · refine ⟨‖c - ρ‖ + 1, by linarith, ?_⟩
      intro t ht
      rw [hTe] at ht
      exact absurd ht (Set.notMem_empty t)
    · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {ρ}) (fun w => ‖c - w‖)
        (hF.subset Set.sdiff_subset) hTne
      exact ⟨‖c - t₀‖, hT t₀ ht₀, htmin⟩
  refine ⟨γ, ρ, hρF.1, min r D, lt_min hr (by linarith), min_le_right _ _, ?_⟩
  intro w hw hb
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hb
  have hwF : w ∈ F := by
    refine ⟨hw, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have := norm_add_le (w - c) (c - c₀)
    rw [sub_add_sub_cancel, norm_sub_rev w c, hcc₀] at this
    linarith [min_le_right r D]
  by_contra hne
  have h3 := hrT w ⟨hwF, hne⟩
  linarith [min_le_left r D]

private theorem eq_ofReal_sub_of_dist_le_of_le_sub_re {w : ℂ} {σ D : ℝ} (h1 : dist w (σ : ℂ) ≤ D) (h2 : D ≤ σ - w.re) :
    w = ((σ - D : ℝ) : ℂ) := by
  have hD0 : 0 ≤ D := dist_nonneg.trans h1
  rw [Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im] at h1
  have hq : (w.re - σ) ^ 2 + (w.im - 0) ^ 2 ≤ D ^ 2 := by
    have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ (w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    have h0 := Real.sqrt_nonneg ((w.re - σ) ^ 2 + (w.im - 0) ^ 2)
    nlinarith
  have him : w.im = 0 := by nlinarith [sq_nonneg w.im]
  have hre : w.re = σ - D := by nlinarith [sq_nonneg w.im]
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him

private theorem landau_dichotomy {Z : Set ℂ} (hiso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {σ θ : ℝ}
    (hθ : 0 < θ) {ρ₀ : ℂ} (h₀ : ρ₀ ∈ Z) (hρ₀ : θ < ρ₀.re) :
    (∃ D : ℝ, D ≤ σ - θ ∧ (∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) D) ∧ ∃ ρ₁ ∈ Z, σ - ρ₁.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ r : ℝ, σ - β < r ∧ r ≤ σ - θ ∧
      ∀ w ∈ Z, w ∈ Metric.ball (σ : ℂ) r → w = β) := by
  have hfin : (Z ∩ Metric.closedBall (σ : ℂ) (σ - θ)).Finite :=
    landau_finite hiso (by rw [Complex.ofReal_re]; linarith)
  set F := Z ∩ Metric.closedBall (σ : ℂ) (σ - θ) with hFdef
  rcases F.eq_empty_or_nonempty with hF | hF
  · left
    refine ⟨σ - θ, le_rfl, ?_, ρ₀, h₀, by linarith⟩
    intro w hw hb
    have hwF : w ∈ F := ⟨hw, Metric.ball_subset_closedBall hb⟩
    rw [hF] at hwF
    exact hwF
  · obtain ⟨ρs, hρsF, hmin⟩ := Set.exists_min_image F (fun w => dist w (σ : ℂ)) hfin hF
    have hdle : dist ρs (σ : ℂ) ≤ σ - θ := Metric.mem_closedBall.mp hρsF.2
    have hball : ∀ w ∈ Z, w ∉ Metric.ball (σ : ℂ) (dist ρs (σ : ℂ)) := by
      intro w hw hb
      rw [Metric.mem_ball] at hb
      have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (by linarith)⟩
      have := hmin w hwF
      linarith
    by_cases hex : ∃ ρ₁ ∈ Z, σ - ρ₁.re < dist ρs (σ : ℂ)
    · left
      exact ⟨dist ρs (σ : ℂ), hdle, hball, hex⟩
    · right
      push Not at hex
      set d := dist ρs (σ : ℂ) with hd
      have hreal : ∀ w ∈ F, dist w (σ : ℂ) = d → w = ((σ - d : ℝ) : ℂ) :=
        fun w hw he => eq_ofReal_sub_of_dist_le_of_le_sub_re (le_of_eq he) (hex w hw.1)
      have hρs := hreal ρs hρsF rfl
      have hdlt : d < σ - θ := by
        rcases lt_or_eq_of_le hdle with h | h
        · exact h
        · exfalso
          have := hex ρ₀ h₀
          linarith
      refine ⟨σ - d, hρs ▸ hρsF.1, by linarith, ?_⟩
      have hT : ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, d < dist t (σ : ℂ) := by
        intro t ht
        have hm : d ≤ dist t (σ : ℂ) := hmin t ht.1
        rcases lt_or_eq_of_le hm with h | h
        · exact h
        · exact absurd (hreal t ht.1 h.symm) ht.2
      obtain ⟨r, hr, hrT⟩ : ∃ r, d < r ∧ ∀ t ∈ F \ {((σ - d : ℝ) : ℂ)}, r ≤ dist t (σ : ℂ) := by
        rcases (F \ {((σ - d : ℝ) : ℂ)}).eq_empty_or_nonempty with hTe | hTne
        · refine ⟨d + 1, by linarith, ?_⟩
          intro t ht
          rw [hTe] at ht
          exact absurd ht (Set.notMem_empty t)
        · obtain ⟨t₀, ht₀, htmin⟩ := Set.exists_min_image (F \ {((σ - d : ℝ) : ℂ)})
            (fun w => dist w (σ : ℂ)) (hfin.subset Set.sdiff_subset) hTne
          exact ⟨dist t₀ (σ : ℂ), hT t₀ ht₀, htmin⟩
      refine ⟨min r (σ - θ), ?_, min_le_right _ _, ?_⟩
      · rw [sub_sub_cancel]
        exact lt_min hr hdlt
      · intro w hw hb
        rw [Metric.mem_ball] at hb
        have hwF : w ∈ F := ⟨hw, Metric.mem_closedBall.mpr (le_trans hb.le (min_le_right _ _))⟩
        by_contra hne
        have h3 := hrT w ⟨hwF, hne⟩
        have h4 := min_le_left r (σ - θ)
        linarith

private theorem landau_cauchy {Φ : ℂ → ℂ} {z : ℂ} {r r' : ℝ} (hd : DifferentiableOn ℂ Φ (Metric.ball z r))
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k Φ z / (k.factorial : ℂ)‖ ≤ M / r' ^ k := by
  set R : NNReal := ⟨r', h0.le⟩ with hRdef
  have hR : (R : ℝ) = r' := rfl
  refine ⟨(2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z r' θ)‖, fun k => ?_⟩
  have hsub : Metric.closedBall z (R : ℝ) ⊆ Metric.ball z r := by
    rw [hR]; exact Metric.closedBall_subset_ball h1
  have hRpos : (0 : NNReal) < R := by
    show (0 : ℝ) < (R : ℝ); rw [hR]; exact h0
  have hp := (hd.mono hsub).hasFPowerSeriesOnBall hRpos
  have key := hp.factorial_smul (1 : ℂ) k
  have hderiv : iteratedDeriv k Φ z / (k.factorial : ℂ) = cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← key, nsmul_eq_mul]
    have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hderiv]
  calc ‖cauchyPowerSeries Φ z (R : ℝ) k (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries Φ z (R : ℝ) k‖ * ∏ _i : Fin k, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries Φ z (R : ℝ) k‖ := by simp
    _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖Φ (circleMap z (R : ℝ) θ)‖) * |(R : ℝ)|⁻¹ ^ k :=
        norm_cauchyPowerSeries_le _ _ _ _
    _ = _ := by
        rw [hR, abs_of_pos h0, inv_pow, div_eq_mul_inv]

private theorem landau_pole_asym_deriv (c ρ z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ => c * (s - ρ)⁻¹) z
      = c * ((-1) ^ k * (k.factorial : ℂ) * ((z - ρ) ^ (k + 1))⁻¹) := by
  rw [iteratedDeriv_const_mul_field]
  congr 1
  have e := congrFun (iteratedDeriv_comp_sub_const k (fun t : ℂ => t⁻¹) ρ) z
  rw [e, iteratedDeriv_eq_iterate, show (fun t : ℂ => t⁻¹) = Inv.inv from rfl, iter_deriv_inv,
    show (-1 - k : ℤ) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]

private theorem landau_pole_asym {Φ : ℂ → ℂ} {z ρ c : ℂ} {r r' : ℝ} (hne : ρ ≠ z)
    (hd : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}))
    (hp : ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s)
    (h0 : 0 < r') (h1 : r' < r) :
    ∃ M : ℝ, ∀ k : ℕ,
      ‖(-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ) - c / (z - ρ) ^ (k + 1)‖ ≤ M / r' ^ k := by
  obtain ⟨hfun, han, hev⟩ := hp
  have hopen : IsOpen (Metric.ball z r \ {ρ}) := Metric.isOpen_ball.sdiff isClosed_singleton
  set G : ℂ → ℂ := fun s => if s = ρ then hfun ρ else Φ s - c / (s - ρ) with hG
  have hGeq : G =ᶠ[𝓝 ρ] hfun := by
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      simp [G]
    · simp only [G, ite_eq_right hsρ]
      rw [hs (Set.mem_compl_singleton_iff.mpr hsρ)]
      ring
  have hGd : DifferentiableOn ℂ G (Metric.ball z r) := by
    intro s hs
    by_cases hsρ : s = ρ
    · rw [hsρ]
      exact ((hGeq.differentiableAt_iff).mpr han.differentiableAt).differentiableWithinAt
    · have hmem : s ∈ Metric.ball z r \ {ρ} := ⟨hs, hsρ⟩
      have hΦ : DifferentiableAt ℂ Φ s := (hd s hmem).differentiableAt (hopen.mem_nhds hmem)
      have hloc : G =ᶠ[𝓝 s] fun t => Φ t - c / (t - ρ) := by
        filter_upwards [hopen.mem_nhds hmem] with t ht
        have htρ : t ≠ ρ := ht.2
        simp only [G, ite_eq_right htρ]
      have hd' : DifferentiableAt ℂ (fun t => Φ t - c / (t - ρ)) s :=
        hΦ.sub ((differentiableAt_const c).div
          (differentiableAt_id.sub (differentiableAt_const ρ)) (sub_ne_zero.mpr hsρ))
      exact ((hloc.differentiableAt_iff).mpr hd').differentiableWithinAt
  obtain ⟨M, hM⟩ := landau_cauchy hGd h0 h1
  refine ⟨M, fun k => ?_⟩
  have hzρ : z ≠ ρ := Ne.symm hne
  have hr : 0 < r := lt_trans h0 h1
  have hmemz : z ∈ Metric.ball z r \ {ρ} := ⟨Metric.mem_ball_self hr, hzρ⟩
  have hloc : Φ =ᶠ[𝓝 z] G + fun s => c * (s - ρ)⁻¹ := by
    filter_upwards [hopen.mem_nhds hmemz] with t ht
    have htρ : t ≠ ρ := ht.2
    simp only [Pi.add_apply, G, ite_eq_right htρ, div_eq_mul_inv]
    ring
  have hGc : ContDiffAt ℂ k G z :=
    (hGd.contDiffOn Metric.isOpen_ball).contDiffAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hPc : ContDiffAt ℂ k (fun s => c * (s - ρ)⁻¹) z := by
    have hs : ContDiffAt ℂ k (fun s : ℂ => s - ρ) z := contDiffAt_id.sub contDiffAt_const
    exact contDiffAt_const.mul (hs.inv (sub_ne_zero.mpr hzρ))
  rw [hloc.iteratedDeriv_eq, iteratedDeriv_add hGc hPc, landau_pole_asym_deriv]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpow : ((-1 : ℂ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  set iG := iteratedDeriv k G z
  set X := (z - ρ) ^ (k + 1)
  have e : (-1) ^ k * (iG + c * ((-1) ^ k * (k.factorial : ℂ) * X⁻¹)) / (k.factorial : ℂ) - c / X
      = (-1) ^ k * (iG / k.factorial) := by
    calc _ = (-1) ^ k * (iG / k.factorial) + ((-1) ^ k * (-1) ^ k) * c *
          ((k.factorial : ℂ) / k.factorial) * X⁻¹ - c / X := by ring
      _ = _ := by rw [hpow, div_self hfac, div_eq_mul_inv c]; ring
  rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hM k

private theorem landau_window_contra {c d e E M C : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hde : d < e) (heE : e ≤ E)
    (h : ∀ k₀ : ℕ, ∃ k ≥ k₀, c / d ^ k ≤ M / e ^ k + C / E ^ k) : False := by
  have he := hd.trans hde
  have hg := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hd).mpr hde)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hg.eventually_gt_atTop ((|M| + |C|) / c))
  obtain ⟨k, hk, hbound⟩ := h k₀
  have hlarge := (div_lt_iff₀ hc).mp (hk₀ k hk)
  rw [div_pow] at hlarge
  have he' := pow_pos he k
  have hsmall : c / d ^ k ≤ (|M| + |C|) / e ^ k := by
    rw [add_div]
    exact hbound.trans (add_le_add (div_le_div_of_nonneg_right (le_abs_self _) he'.le)
      (div_le_div₀ (abs_nonneg _) (le_abs_self _) he' (pow_le_pow_left₀ he.le heE k)))
  have hsmall' := (div_le_div_iff₀ (pow_pos hd k) he').mp hsmall
  rw [div_mul_eq_mul_div, lt_div_iff₀ (pow_pos hd k)] at hlarge
  linarith

private theorem landau_window_key {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z)
    {θ δ B : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ B * Real.exp (θ * u)) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ k₀ : ℕ, ∃ k ≥ k₀, ∀ γ : ℝ,
      ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤ C / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, T, ht⟩ := landau_tails hδ
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀pos : 0 ≤ C₀ := (abs_nonneg _).trans (by simpa using hC₀ 0 le_rfl)
  have ha : 0 < σ - θ := by linarith
  refine ⟨σ, hσ, 2 * B / (σ - θ) + 2 * C₀ * |T|, fun k₀ => ?_⟩
  obtain ⟨U, hU, hw⟩ := hW (max (k₀ : ℝ) 1)
  have hu := (le_max_right _ _).trans hU
  obtain ⟨k, hk, htail⟩ := ht U hu
  refine ⟨k, by exact_mod_cast ((le_max_left _ _).trans hU).trans hk, fun γ => ?_⟩
  have h := landau_window_ineq hB hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith) hw k γ
  rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
    landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
  have hscale : T / σ ^ k ≤ |T| / (σ - θ) ^ k :=
    div_le_div₀ (abs_nonneg _) (le_abs_self _) (pow_pos ha _) (pow_le_pow_left₀ ha.le (by linarith) k)
  have hcost := mul_le_mul_of_nonneg_left (htail.trans hscale) (by positivity : 0 ≤ 2 * C₀)
  rw [pow_succ, mul_inv] at h
  rw [add_div]
  simp only [div_eq_mul_inv] at h hcost ⊢
  linarith only [h, hcost]

private theorem landau_window_re_pos {z w : ℂ} {r : ℝ} (hr : r ≤ z.re) (hw : w ∈ Metric.ball z r) :
    0 < w.re := by
  have h1 : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
  have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  have h3 := (abs_lt.mp (h2.trans_lt h1)).1
  simp only [Complex.sub_re] at h3
  linarith

/-- The analytic pole-exclusion step consumes cofinally many jointly
controlled Laplace coefficients. It has no pointwise window hypothesis. -/
theorem landau_of_coefficients {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {θ : ℝ} (hθ : 0 < θ) (_hθ1 : θ < 1)
    (hK : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ k₀ : ℕ, ∃ k ≥ k₀, ∀ γ : ℝ,
      ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
          C / (σ - θ) ^ k) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ₀ h₀
  by_contra hρ₀
  rw [not_le] at hρ₀
  obtain ⟨σ, hσ, C, hkey⟩ := hK
  have hle : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (hP.right ρ hρ).trans (by linarith)
  rcases landau_dichotomy hP.iso hθ h₀ hρ₀ with
    ⟨D, hD, hfree, ρ₁, h₁, hρ₁⟩ | ⟨β, hβZ, hβ, r, hr1, hr2, huniq⟩
  · obtain ⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩ := landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁
    obtain ⟨c, hc, -, hp⟩ := hP.pole ρ hρ
    set z : ℂ := (σ : ℂ) + γ * I with hz
    have hzre : z.re = σ := by simp [hz]
    have hne : ρ ≠ z := by
      intro h
      have := hle ρ hρ
      rw [h, hzre] at this
      exact lt_irrefl _ this
    have hd : 0 < ‖z - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
    set d := ‖z - ρ‖ with hddef
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [hzre]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩
    have hdiff' : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D) := by
      refine hP.diff.mono ?_
      intro w hw
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hfree w hZ hw⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hne hdiff hp (by linarith) (by linarith)
    obtain ⟨M', hM'⟩ := landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)
    refine landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ) (M := M + M') (C := C)
      (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith) fun k₀ => ?_
    obtain ⟨k, hk, hb⟩ := hkey k₀
    refine ⟨k, hk, ?_⟩
    have h1 := hb γ
    have h2 := hM k
    have h3 := hM' k
    have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k := by
      rw [norm_div, norm_pow, pow_succ', div_div]
    have h5 : ‖(-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖
        = ‖iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖ := by
      rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)))).1
    have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
      ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))
    rw [norm_sub_rev] at h7
    rw [add_div]
    linarith
  · obtain ⟨c, -, hc, hp⟩ := hP.pole β hβZ
    obtain ⟨hc1, hc2⟩ := hc (Complex.ofReal_im β)
    have hd : 0 < σ - β := by
      have := hle β hβZ
      rw [Complex.ofReal_re] at this
      linarith
    have hne : (β : ℂ) ≠ (σ : ℂ) := by
      intro h
      have : β = σ := by exact_mod_cast h
      linarith
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) r \ {(β : ℂ)}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw,
        fun hZ => hw' (huniq w hZ hw)⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ)
      (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun k₀ => ?_
    obtain ⟨k, hk, hb⟩ := hkey k₀
    refine ⟨k, hk, ?_⟩
    have h1 := hb 0
    have h2 := hM k
    have h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1
    rw [Complex.sub_re, h4] at h6
    have h7 := norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))
    linarith

/-- A bound on cofinally many weighted positive first moments of the
complete signed source excludes poles to the right of `θ`. Neither a
pointwise bound nor a window bound is an assumption of this theorem. -/
theorem landau_of_positiveMoments {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hP : PoleData g Φ Z) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hM : ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k₀ : ℕ, ∃ k ≥ k₀,
        weightedPositiveMoment g σ k ≤ C / (σ - θ) ^ k) :
    ∀ ρ ∈ Z, ρ.re ≤ θ := by
  apply landau_of_coefficients hP hθ hθ1
  obtain ⟨σ, hσ, C, _hC, hmoment⟩ := hM
  refine ⟨σ, hσ, 2 * C, fun k₀ => ?_⟩
  obtain ⟨k, hk, hbound⟩ := hmoment k₀
  refine ⟨k, hk, fun γ => ?_⟩
  calc
    _ ≤ 2 * weightedPositiveMoment g σ k :=
      landau_coefficients_le_positiveMoment hP hσ k γ
    _ ≤ 2 * (C / (σ - θ) ^ k) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (2 * C) / (σ - θ) ^ k := by ring

/-- The original window theorem retains its complete public hypothesis
telescope; its analytic conclusion now uses the reusable coefficient step. -/
theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ B : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hW : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U), g u ≤ B * Real.exp (θ * u)) : ∀ ρ ∈ Z, ρ.re ≤ θ :=
  landau_of_coefficients hP hθ hθ1 (landau_window_key hP hθ hθ1 hδ hB hW)

end RHLean.Analysis.WindowLandau
