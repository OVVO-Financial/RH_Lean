import Mathlib

/-!
# Gaussian summation and Fourier uniqueness for native theta sections

This file proves the analytic tools needed for the actual native period
lattice: coercivity of a positive complex matrix form, Gaussian summability
on a discrete integral lattice, holomorphy of a locally normally convergent
series, and uniqueness of the absolutely convergent Fourier expansion on
a finite dimensional real torus. No theta section or bound is assumed.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CovolumeBounds/`
`SummableLatticeExpNegPiMulNormSqDiv.lean` and
`DifferentiableOnOfTendstoLocallyUniformlyOn.lean`, and
`Proofs/TorusSplitting/CoeffEqZeroOfOrthonormal.lean` and
`Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean`.
Only the needed proofs are reconstructed over Mathlib. The source mirror
states no license; attribution is preserved without assigning one. No
upstream compiled object or terminal RH theorem is imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Metric Set Filter
open scoped BigOperators Topology

namespace RHLean.Geometry.NativeTheta.GaussianSeries

section Coercivity

variable {g : ℕ}

/-- The real quadratic form of the actual period matrix is continuous. -/
theorem continuous_form (M : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (z ⬝ᵥ M.mulVec (star z)).re := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- Positive definiteness supplies an actual Gaussian decay constant for
the ambient default norm; no Euclidean replacement of the period is needed. -/
theorem exists_coercive (M : Matrix (Fin g) (Fin g) ℂ)
    (hM : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (z ⬝ᵥ M.mulVec (star z)).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin g → ℂ,
      c * ‖z‖ ^ 2 ≤ (z ⬝ᵥ M.mulVec (star z)).re := by
  obtain ⟨c, hc, h⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le'
    (continuous_form M).continuousOn (a := 0) fun z hz => hM z (by
      rintro rfl
      simp at hz)
  refine ⟨c, hc, fun z => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨u, hu, hzu⟩ : ∃ u : Fin g → ℂ, ‖u‖ = 1 ∧ z = (‖z‖ : ℝ) • u :=
    ⟨‖z‖⁻¹ • z, by rw [norm_smul]; simp [hn.ne'], by simp [smul_smul, hn.ne']⟩
  have h2 := h u (by simpa using hu)
  have hscale (r : ℝ) (v : Fin g → ℂ) :
      ((r • v) ⬝ᵥ M.mulVec (star (r • v))).re =
        r ^ 2 * (v ⬝ᵥ M.mulVec (star v)).re := by
    rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
    ring
  have hform : (z ⬝ᵥ M.mulVec (star z)).re =
      ‖z‖ ^ 2 * (u ⬝ᵥ M.mulVec (star u)).re := by
    calc
      (z ⬝ᵥ M.mulVec (star z)).re =
          (((‖z‖ : ℝ) • u) ⬝ᵥ M.mulVec (star ((‖z‖ : ℝ) • u))).re :=
        congrArg (fun v : Fin g → ℂ => (v ⬝ᵥ M.mulVec (star v)).re) hzu
      _ = ‖z‖ ^ 2 * (u ⬝ᵥ M.mulVec (star u)).re := hscale ‖z‖ u
  calc
    c * ‖z‖ ^ 2 ≤ (u ⬝ᵥ M.mulVec (star u)).re * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = (z ⬝ᵥ M.mulVec (star z)).re := by rw [hform, mul_comm]

end Coercivity

section Gaussian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]

/-- The Gaussian on the actual discrete lattice is summable. -/
theorem summable_gaussian {a : ℝ} (ha : 0 < a) :
    Summable fun x : L => Real.exp (-a * ‖(x : V)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : V)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : V)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- One fixed summable Gaussian dominates all bounded translates. -/
theorem gaussian_translate_le {a R : ℝ} (ha : 0 ≤ a) (x : V) {u : V}
    (hu : ‖u‖ ≤ R) :
    Real.exp (-a * ‖x + u‖ ^ 2) ≤
      Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : ‖x‖ ≤ ‖x + u‖ + R := by
    have := norm_sub_le (x + u) u
    rw [add_sub_cancel_right] at this
    linarith
  have h2 : ‖x‖ ^ 2 ≤ (‖x + u‖ + R) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ‖x‖ ^ 2 / 2 ≤ ‖x + u‖ ^ 2 + R ^ 2 := by
    nlinarith [sq_nonneg (‖x + u‖ - R)]
  nlinarith [mul_le_mul_of_nonneg_left h3 ha]

end Gaussian

section Holomorphy

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

private theorem norm_fderiv_le_of_ball {f : V → W} {c : V} {r M : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f c‖ ≤ 2 * M / r := by
  refine Complex.norm_fderiv_le_div_of_mapsTo_ball hf (fun z hz => ?_) hr
  rw [mem_closedBall_iff_norm]
  have := norm_sub_le (f z) (f c)
  linarith [hM z hz, hM c (mem_ball_self hr)]

private theorem tendstoUniformlyOn_fderiv_ball [CompleteSpace W]
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → V → W} {f : V → W} {c : V} {r : ℝ}
    (hlim : TendstoUniformlyOn F f l (ball c (2 * r)))
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) (ball c (2 * r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.mpr hr, differentiableOn_empty, tendstoUniformlyOn_empty]
  have hsub : ∀ x ∈ ball c r, ball x r ⊆ ball c (2 * r) := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hC : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) l (ball c r) := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
    have h1 := hlim.uniformCauchySeqOn _
      (Metric.dist_mem_uniformity (ε := ε * r / 4) (by positivity))
    filter_upwards [h1, hF.prod_inl l, hF.prod_inr l] with m hm hm1 hm2 x hx
    apply hεu
    have hn : ball c (2 * r) ∈ 𝓝 x :=
      mem_of_superset (ball_mem_nhds x hr) (hsub x hx)
    rw [dist_eq_norm, ← fderiv_sub (hm1.differentiableAt hn) (hm2.differentiableAt hn)]
    have := norm_fderiv_le_of_ball (f := F m.1 - F m.2) (M := ε * r / 4) hr
      ((hm1.sub hm2).mono (hsub x hx)) (fun z hz => by
        have := hm z (hsub x hx hz)
        simp only [dist_eq_norm] at this
        exact this.le)
    refine this.trans_lt ?_
    rw [div_lt_iff₀ hr]
    nlinarith [mul_pos hε hr]
  set g' : V → V →L[ℂ] W := fun x => limUnder l (fun n => fderiv ℂ (F n) x)
  have hT : TendstoUniformlyOn (fun n => fderiv ℂ (F n)) g' l (ball c r) :=
    hC.tendstoUniformlyOn_of_tendsto fun x hx => (hC.cauchy_map hx).le_nhds_lim
  have hsub' : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  have hD : ∀ x ∈ ball c r, HasFDerivAt f (g' x) x := by
    intro x hx
    have hn : ball c r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F)
      (f' := fun n => fderiv ℂ (F n)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hT).mono_right
        (le_principal_iff.mpr hn)
    · filter_upwards [hF.prod_inl _, Filter.Eventually.prod_inr hn l] with p hp hp2
      exact (hp.differentiableAt (isOpen_ball.mem_nhds (hsub' hp2))).hasFDerivAt
    · filter_upwards [hn] with y hy using hlim.tendsto_at (hsub' hy)
  exact ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,
    hT.congr_right fun x hx => (hD x hx).fderiv.symm⟩

variable [FiniteDimensional ℂ V] [CompleteSpace W]
  {ι : Type*} {l : Filter ι} {F : ι → V → W} {f : V → W} {U : Set V}

private theorem exists_ball_limit [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    {c : V} (hc : c ∈ U) : ∃ r > 0, DifferentiableOn ℂ f (ball c r) := by
  have : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  have hsub : closedBall c (2 * (R / 4)) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hRU
  have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hsub
    (isCompact_closedBall _ _)
  exact ⟨R / 4, by positivity,
    (tendstoUniformlyOn_fderiv_ball (h1.mono ball_subset_closedBall)
      (hF.mono fun n hn => hn.mono (ball_subset_closedBall.trans hsub))).1⟩

theorem differentiableOn_of_tendstoLocallyUniformlyOn [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U)
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by
  intro c hc
  obtain ⟨r, hr, h⟩ := exists_ball_limit hU hlim hF hc
  exact (h.differentiableAt (ball_mem_nhds c hr)).differentiableWithinAt

theorem differentiableOn_of_hasSumLocallyUniformlyOn (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    DifferentiableOn ℂ f U :=
  differentiableOn_of_tendstoLocallyUniformlyOn hU
    (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hsum)
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i)

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedSpace ℂ W] in
theorem hasSumLocallyUniformlyOn_of_locally_normal
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ,
      Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    HasSumLocallyUniformlyOn F (fun z => ∑' i, F i z) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  obtain ⟨t, ht, u, hu, h⟩ := hle x hx
  exact ⟨t, nhdsWithin_le_nhds ht, tendstoUniformlyOn_tsum hu h⟩

/-- Holomorphy follows from an actual summable local bound. -/
theorem differentiableOn_tsum_of_locally_normal (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ,
      Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U :=
  differentiableOn_of_hasSumLocallyUniformlyOn hU
    (hasSumLocallyUniformlyOn_of_locally_normal hle) hF

end Holomorphy

section Fourier

private theorem coeff_eq_zero_of_orthonormal
    {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ}
    (hs : HasSum (fun i => c i • e i) 0) (k : κ) : c k = 0 := by
  classical
  have h1 := ((innerSL ℂ (T (e k))).comp T).hasSum hs
  simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, map_zero,
    orthonormal_iff_ite.1 h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  have h2 : HasSum (fun i => if k = i then c i else 0) (c k) := by
    convert hasSum_ite_eq k (c k) using 2 with i
    by_cases hi : k = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  exact h2.unique h1

/-- Absolutely convergent torus Fourier coefficients are unique. -/
theorem coeff_eq_zero_of_fourier {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ,
      ∑' n, c n * Complex.exp
        (2 * Real.pi * Complex.I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by
  refine coeff_eq_zero_of_orthonormal _ UnitAddTorus.mFourier
    (UnitAddTorus.orthonormal_mFourier (d := d)) ?_ k
  have hs : Summable fun n => c n • UnitAddTorus.mFourier n :=
    .of_norm (by simpa [norm_smul, UnitAddTorus.mFourier_norm] using hc)
  suffices h : (0 : C(UnitAddTorus d, ℂ)) = ∑' n, c n • UnitAddTorus.mFourier n from
    h ▸ hs.hasSum
  ext x
  have hx : ∃ t : d → ℝ, x = fun j => (t j : UnitAddCircle) := by
    choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
    exact ⟨t, funext fun j => (ht j).symm⟩
  obtain ⟨t, rfl⟩ := hx
  rw [← ContinuousMap.tsum_apply hs, ContinuousMap.zero_apply, ← h0 t]
  refine tsum_congr fun n => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, fourier_coe_apply, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Fourier

end RHLean.Geometry.NativeTheta.GaussianSeries

end
