import «research.UNIVERSAL_ENVELOPE_LAWS»
import «research.NATIVE_OWNER_PREFIX_MERTENS_20261021»

/-!
# The actual uncentered Mertens prefix budget

For B >= 2 this is exactly max_{1 <= n < B} |M(n)| / sqrt(n).
The existing native prefix-amplitude definition adjoins the value one only
to extend it to empty ranges; the n=1 summand already equals one for B>=2.
The source is the actual uncentered Mertens function, not shifted history.

Uniform comparisons with the original centered K_B transport its exponent
law to this full-prefix budget.  The fixed-degree critical lift follows with
one constant for every positive loss, fixed before the root B.
-/

noncomputable section

namespace RHLean.Analysis.UniversalEnvelope

open Filter RHLean.Proof RHLean.Analysis.MertensExponent
open RHLean.Analysis.OwnerPrefix

/-- The actual uncentered full-prefix budget, extended by one on empty ranges. -/
def mertensPrefixBudget (B : ℕ) : ℝ := prefixAmplitude nativeM B

theorem mertensPrefixBudget_one_le (B : ℕ) : 1 ≤ mertensPrefixBudget B :=
  one_le_prefixAmplitude nativeM B

theorem mertensPrefixBudget_nonneg (B : ℕ) : 0 ≤ mertensPrefixBudget B :=
  zero_le_one.trans (mertensPrefixBudget_one_le B)

theorem mertensPrefixBudget_pos (B : ℕ) : 0 < mertensPrefixBudget B :=
  zero_lt_one.trans_le (mertensPrefixBudget_one_le B)

/-- For every relevant cutoff the adjoined one is already an actual summand. -/
theorem mertensPrefixBudget_eq_raw (B : ℕ) (hB : 2 ≤ B) :
    mertensPrefixBudget B = rawPrefixAmplitude nativeM B hB :=
  native_prefixAmplitude_eq_raw B hB

/-- Exact least-upper-bound characterization in the original complex Mertens
coordinate.  This identifies the budget with the literal strict-prefix max. -/
theorem mertensPrefixBudget_le_iff (B : ℕ) (hB : 2 ≤ B) (C : ℝ) :
    mertensPrefixBudget B ≤ C ↔
      ∀ n : ℕ, 1 ≤ n → n < B →
        ‖mertensSummatory n‖ / Real.sqrt (n : ℝ) ≤ C := by
  constructor
  · intro hC n hn hnB
    have hs : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    have h := abs_le_prefixAmplitude_mul_sqrt nativeM hn hnB
    rw [nativeM_abs_eq_norm] at h
    exact ((div_le_iff₀ hs).mpr h).trans hC
  · intro h
    have hunit := h 1 (by omega) (by omega)
    rw [← nativeM_abs_eq_norm, nativeM_one] at hunit
    have hC : 1 ≤ C := by simpa using hunit
    apply prefixAmplitude_le nativeM hC
    intro n hn hnB
    rw [nativeM_abs_eq_norm]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr
      (by exact_mod_cast (show 0 < n by omega)))).mp (h n hn hnB)

/-- Centering changes the squared historical budget by at most a fixed factor. -/
theorem historical_le_four_prefixBudget_sq (B : ℕ) :
    squareRootHistoricalK B ≤ 4 * mertensPrefixBudget B ^ 2 := by
  have hE1 := mertensPrefixBudget_one_le B
  have hE0 := mertensPrefixBudget_nonneg B
  apply (squareRootHistoricalK_le_iff B _).mpr
  refine ⟨by positivity, ?_⟩
  intro n hnB
  have hs1 : 1 ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    simpa using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hM : ‖mertensSummatory n‖ ≤
      mertensPrefixBudget B * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    by_cases hn : n = 0
    · subst n
      rw [mertensSummatory_zero, norm_zero]
      positivity
    · have h := abs_le_prefixAmplitude_mul_sqrt nativeM
        (show 1 ≤ n by omega) hnB
      rw [nativeM_abs_eq_norm] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n)) hE0)
  have hunit : 1 ≤ mertensPrefixBudget B * Real.sqrt ((n + 1 : ℕ) : ℝ) :=
    hs1.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hE1 (Real.sqrt_nonneg _))
  have hcenter : ‖mertensSummatory n - 1‖ ≤
      (2 * mertensPrefixBudget B) * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    have htri := norm_sub_le (mertensSummatory n) (1 : ℂ)
    simp only [norm_one] at htri
    nlinarith only [htri, hM, hunit]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hcenter
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  rw [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy]
  nlinarith only [hsq]

/-- The actual uncentered budget is controlled by the centered history. -/
theorem prefixBudget_le_three_sqrt_historical (B : ℕ) (hB : 2 ≤ B) :
    mertensPrefixBudget B ≤ 3 * Real.sqrt (squareRootHistoricalK B) := by
  have hK0 := squareRootHistoricalK_nonneg B
  have hKs1 : 1 ≤ Real.sqrt (squareRootHistoricalK B) := by
    simpa using Real.sqrt_le_sqrt (squareRootHistoricalK_one_le (show 1 ≤ B by omega))
  apply prefixAmplitude_le nativeM (by linarith only [hKs1])
  intro n hn hnB
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hns1 : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hn1
  have hcenter : ‖mertensSummatory n - 1‖ ^ 2 ≤
      squareRootHistoricalK B * ((n + 1 : ℕ) : ℝ) := by
    have h := (squareRootHistoricalK_envelope B).2 n hnB
    simpa only [← shiftedMertensEnergy_eq_intSquare, shiftedMertensEnergy] using h
  have hcenterRoot : ‖mertensSummatory n - 1‖ ≤
      2 * Real.sqrt (squareRootHistoricalK B) * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖mertensSummatory n - 1‖ ^ 2 ≤
          squareRootHistoricalK B * ((n + 1 : ℕ) : ℝ) := hcenter
      _ ≤ squareRootHistoricalK B * (4 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (by push_cast; linarith only [hn1]) hK0
      _ = (2 * Real.sqrt (squareRootHistoricalK B) * Real.sqrt (n : ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt (Nat.cast_nonneg n)]
        ring
  have hunit : 1 ≤ Real.sqrt (squareRootHistoricalK B) * Real.sqrt (n : ℝ) :=
    hns1.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hKs1 (Real.sqrt_nonneg _))
  rw [nativeM_abs_eq_norm]
  have htri : ‖mertensSummatory n‖ ≤ ‖mertensSummatory n - 1‖ + 1 := by
    have h := norm_add_le (mertensSummatory n - 1) (1 : ℂ)
    simpa only [sub_add_cancel, norm_one] using h
  nlinarith only [htri, hcenterRoot, hunit]

theorem prefixBudget_sq_le_nine_historical (B : ℕ) (hB : 2 ≤ B) :
    mertensPrefixBudget B ^ 2 ≤ 9 * squareRootHistoricalK B := by
  have h := (sq_le_sq₀ (mertensPrefixBudget_nonneg B) (by positivity)).mpr
    (prefixBudget_le_three_sqrt_historical B hB)
  rw [mul_pow, Real.sq_sqrt (squareRootHistoricalK_nonneg B)] at h
  nlinarith only [h]

/-- Every positive tolerance supplies a uniform upper power for the literal E. -/
theorem prefixBudget_upper_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B →
      mertensPrefixBudget B ≤ C * (B : ℝ) ^ (envelopeExponent + ε) := by
  obtain ⟨C, hC, hK⟩ := historical_upper_power (2 * ε) (by linarith)
  refine ⟨3 * Real.sqrt C, by positivity, ?_⟩
  intro B hB
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hpower : ((B : ℝ) ^ (envelopeExponent + ε)) ^ (2 : ℕ) =
      (B : ℝ) ^ (2 * envelopeExponent + 2 * ε) := by
    rw [← Real.rpow_mul_natCast hB0.le (envelopeExponent + ε) 2]
    congr 1
    ring
  apply (sq_le_sq₀ (mertensPrefixBudget_nonneg B) (by positivity)).mp
  calc
    mertensPrefixBudget B ^ 2 ≤ 9 * squareRootHistoricalK B :=
      prefixBudget_sq_le_nine_historical B hB
    _ ≤ 9 * (C * (B : ℝ) ^ (2 * envelopeExponent + 2 * ε)) :=
      mul_le_mul_of_nonneg_left (hK B (by omega)) (by norm_num)
    _ = (3 * Real.sqrt C * (B : ℝ) ^ (envelopeExponent + ε)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, hpower]
      ring

/-- A uniform lower power, in a form that also covers the finite initial range. -/
theorem prefixBudget_power_le_scaled (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ B : ℕ, 2 ≤ B →
      (B : ℝ) ^ (envelopeExponent - ε) ≤ D * mertensPrefixBudget B := by
  obtain ⟨D, hD, hK⟩ := historical_power_le_scaled (2 * ε) (by linarith)
  refine ⟨2 * Real.sqrt D, by positivity, ?_⟩
  intro B hB
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hE0 := mertensPrefixBudget_nonneg B
  have hpower : ((B : ℝ) ^ (envelopeExponent - ε)) ^ (2 : ℕ) =
      (B : ℝ) ^ (2 * envelopeExponent - 2 * ε) := by
    rw [← Real.rpow_mul_natCast hB0.le (envelopeExponent - ε) 2]
    congr 1
    ring
  apply (sq_le_sq₀ (Real.rpow_nonneg hB0.le _) (by positivity)).mp
  calc
    ((B : ℝ) ^ (envelopeExponent - ε)) ^ 2 =
        (B : ℝ) ^ (2 * envelopeExponent - 2 * ε) := hpower
    _ ≤ D * squareRootHistoricalK B := hK B (by omega)
    _ ≤ D * (4 * mertensPrefixBudget B ^ 2) :=
      mul_le_mul_of_nonneg_left (historical_le_four_prefixBudget_sq B) hD.le
    _ = (2 * Real.sqrt D * mertensPrefixBudget B) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]
      ring

/-- ENV-3(a) for the original uncentered full-prefix budget. -/
theorem prefixBudget_log_ratio_tendsto :
    Tendsto (fun B : ℕ => Real.log (mertensPrefixBudget B) / Real.log (B : ℝ))
      atTop (nhds envelopeExponent) := by
  have hlogTop : Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε : ℝ := (envelopeExponent - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨D, hD, hlower⟩ := prefixBudget_power_le_scaled ε hε
    have hconst : Tendsto (fun B : ℕ => Real.log D / Real.log (B : ℝ))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogTop
    have hnear := (tendsto_order.mp hconst).2 ε hε
    filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with B hnearB hB
    have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
    have hlogB : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    have h := Real.log_le_log (Real.rpow_pos_of_pos hB0 _) (hlower B hB)
    rw [Real.log_rpow hB0, Real.log_mul hD.ne' (mertensPrefixBudget_pos B).ne'] at h
    have hdivide := div_le_div_of_nonneg_right h hlogB.le
    have hbound : envelopeExponent - ε ≤
        Real.log D / Real.log (B : ℝ) +
          Real.log (mertensPrefixBudget B) / Real.log (B : ℝ) := by
      simpa only [add_div, mul_div_cancel_right₀ _ hlogB.ne'] using hdivide
    dsimp [ε] at hbound hnearB
    linarith only [hbound, hnearB]
  · intro b hb
    let ε : ℝ := (b - envelopeExponent) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨C, hC, hupper⟩ := prefixBudget_upper_power ε hε
    have hconst : Tendsto (fun B : ℕ => Real.log C / Real.log (B : ℝ))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogTop
    have hnear := (tendsto_order.mp hconst).2 ε hε
    filter_upwards [hnear, eventually_ge_atTop (2 : ℕ)] with B hnearB hB
    have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
    have hlogB : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    have h := Real.log_le_log (mertensPrefixBudget_pos B) (hupper B hB)
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hB0 _).ne', Real.log_rpow hB0] at h
    have hdivide := div_le_div_of_nonneg_right h hlogB.le
    have hbound : Real.log (mertensPrefixBudget B) / Real.log (B : ℝ) ≤
        Real.log C / Real.log (B : ℝ) + (envelopeExponent + ε) := by
      simpa only [add_div, mul_div_cancel_right₀ _ hlogB.ne'] using hdivide
    dsimp [ε] at hbound hnearB
    linarith only [hbound, hnearB]

/-- ENV-4 for every fixed integral degree.  The exponent on E(B) is exactly k. -/
theorem prefixBudget_critical_lift (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℕ, 2 ≤ B →
      mertensPrefixBudget (B ^ k) ≤
        C * (B : ℝ) ^ ε * mertensPrefixBudget B ^ k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let δ : ℝ := ε / (2 * (k : ℝ))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : (2 * (k : ℝ)) * δ = ε := by
    dsimp [δ]
    exact mul_div_cancel₀ ε (ne_of_gt (show 0 < 2 * (k : ℝ) by positivity))
  obtain ⟨A, hA, hupper⟩ := prefixBudget_upper_power δ hδ
  obtain ⟨D, hD, hlower⟩ := prefixBudget_power_le_scaled δ hδ
  refine ⟨A * D ^ k, by positivity, ?_⟩
  intro B hB
  have hBk : 2 ≤ B ^ k := hB.trans (Nat.le_self_pow (by omega : k ≠ 0) B)
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hlowPow := pow_le_pow_left₀ (Real.rpow_nonneg hB0.le _) (hlower B hB) k
  rw [mul_pow, ← Real.rpow_mul_natCast hB0.le] at hlowPow
  have hlarge := hupper (B ^ k) hBk
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hB0.le] at hlarge
  have hexp : (k : ℝ) * (envelopeExponent + δ) =
      ε + (envelopeExponent - δ) * (k : ℝ) := by
    nlinarith only [hδeq]
  rw [hexp, Real.rpow_add hB0] at hlarge
  calc
    mertensPrefixBudget (B ^ k) ≤
        A * ((B : ℝ) ^ ε * (B : ℝ) ^ ((envelopeExponent - δ) * (k : ℝ))) := hlarge
    _ ≤ A * ((B : ℝ) ^ ε * (D ^ k * mertensPrefixBudget B ^ k)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlowPow (Real.rpow_nonneg hB0.le _)) hA.le
    _ = (A * D ^ k) * (B : ℝ) ^ ε * mertensPrefixBudget B ^ k := by ring

/-- The k-th endpoint, still normalized by the ORIGINAL root logarithm. -/
theorem prefixBudget_power_log_ratio_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun B : ℕ => Real.log (mertensPrefixBudget (B ^ k)) / Real.log (B : ℝ))
      atTop (nhds ((k : ℝ) * envelopeExponent)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hpow : Tendsto (fun B : ℕ => B ^ k) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_self_pow (by omega : k ≠ 0) B) tendsto_id
  have hlim : Tendsto
      (fun B : ℕ => (k : ℝ) *
        (Real.log (mertensPrefixBudget (B ^ k)) / Real.log ((B ^ k : ℕ) : ℝ)))
      atTop (nhds ((k : ℝ) * envelopeExponent)) :=
    tendsto_const_nhds.mul (prefixBudget_log_ratio_tendsto.comp hpow)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with B hB
  have hlog : Real.log (B : ℝ) ≠ 0 := ne_of_gt
    (Real.log_pos (by exact_mod_cast (show 1 < B by omega)))
  dsimp only [Function.comp_apply]
  rw [Nat.cast_pow, Real.log_pow]
  field_simp [hk0.ne', hlog] <;> ring

/-- The every-root subcritical-lift form, with each positive loss quantified. -/
def MertensPrefixLiftBound (k : ℕ) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B →
    mertensPrefixBudget (B ^ k) ≤
      C * (B : ℝ) ^ ε * (mertensPrefixBudget B) ^ r

/-- The original MU-LIFT scheduling allowance: estimates only along an
unbounded sequence of genuine full-prefix cutoffs, with eventual validity. -/
def MertensPrefixLiftOn (B : ℕ → ℕ) (k : ℕ) (r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
    mertensPrefixBudget ((B j) ^ k) ≤
      C * (B j : ℝ) ^ ε * (mertensPrefixBudget (B j)) ^ r

/-- Critical Mertens growth supplies the lift with any nonnegative budget
power.  No epsilon-free bound on E is used. -/
theorem prefixLiftBound_of_mertens_half (k : ℕ) (hk : 1 ≤ k)
    (r : ℝ) (hr : 0 ≤ r) (hhalf : MertensGrowthAtMost (1 / 2 : ℝ)) :
    MertensPrefixLiftBound k r := by
  have hh := envelopeExponent_eq_zero_iff_mertens_half.mpr hhalf
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  intro ε hε
  obtain ⟨C, hC, hupper⟩ := prefixBudget_upper_power (ε / (k : ℝ)) (div_pos hε hk0)
  refine ⟨C, hC.le, ?_⟩
  intro B hB
  have hBk : 2 ≤ B ^ k := hB.trans (Nat.le_self_pow (by omega : k ≠ 0) B)
  have hB0 : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have h := hupper (B ^ k) hBk
  rw [hh, zero_add, Nat.cast_pow, ← Real.rpow_natCast_mul hB0.le,
    mul_div_cancel₀ ε hk0.ne'] at h
  exact h.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.one_le_rpow (mertensPrefixBudget_one_le B) hr)
      (show 0 ≤ C * (B : ℝ) ^ ε by positivity))

/-- Every-root bounds restrict to any sequence tending to infinity. -/
theorem prefixLiftBound_on {B : ℕ → ℕ} {k : ℕ} {r : ℝ}
    (hB : Tendsto B atTop atTop) (hlift : MertensPrefixLiftBound k r) :
    MertensPrefixLiftOn B k r := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hlift ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hB.eventually (eventually_ge_atTop (2 : ℕ))] with j hj
  exact h (B j) hj

/-- A fixed subcritical budget power on any unbounded sequence forces the
critical boundary.  Thus the proof does not impose every-root uniformity on
the original chain-based MU-LIFT route. -/
theorem mertens_half_of_subcritical_prefixLiftOn
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) (hlift : MertensPrefixLiftOn B k r) :
    MertensGrowthAtMost (1 / 2 : ℝ) := by
  apply envelopeExponent_eq_zero_iff_mertens_half.mp
  by_contra hne
  have hh : 0 < envelopeExponent :=
    lt_of_le_of_ne envelopeExponent_nonneg (Ne.symm hne)
  let ε : ℝ := (((k : ℝ) - r) * envelopeExponent) / 2
  have hε : 0 < ε := by dsimp [ε]; exact div_pos (mul_pos (sub_pos.mpr hrk) hh) (by norm_num)
  obtain ⟨C, hC, hstep⟩ := hlift ε hε
  let D : ℝ := C + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hlogTop : Tendsto (fun j : ℕ => Real.log (B j : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hB
  have hconstant : Tendsto (fun j : ℕ => Real.log D / Real.log (B j : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogTop
  have hleft := (prefixBudget_power_log_ratio_tendsto k hk).comp hB
  have hright := prefixBudget_log_ratio_tendsto.comp hB
  have hrconst : Tendsto (fun _j : ℕ => r) atTop (nhds r) := tendsto_const_nhds
  have hlimit : Tendsto
      (fun j : ℕ =>
        Real.log (mertensPrefixBudget ((B j) ^ k)) / Real.log (B j : ℝ) -
          r * (Real.log (mertensPrefixBudget (B j)) / Real.log (B j : ℝ)) -
          Real.log D / Real.log (B j : ℝ))
      atTop (nhds ((k : ℝ) * envelopeExponent - r * envelopeExponent)) := by
    simpa only [Function.comp_apply, sub_zero] using
      (hleft.sub (hrconst.mul hright)).sub hconstant
  have hevent : ∀ᶠ j : ℕ in atTop,
      Real.log (mertensPrefixBudget ((B j) ^ k)) / Real.log (B j : ℝ) -
        r * (Real.log (mertensPrefixBudget (B j)) / Real.log (B j : ℝ)) -
        Real.log D / Real.log (B j : ℝ) ≤ ε := by
    filter_upwards [hstep, hB.eventually (eventually_ge_atTop (2 : ℕ))] with j hj hj2
    have hBj0 : (0 : ℝ) < (B j : ℝ) := by exact_mod_cast (show 0 < B j by omega)
    have hlog : 0 < Real.log (B j : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B j by omega))
    have hEr0 : 0 ≤ (mertensPrefixBudget (B j)) ^ r :=
      zero_le_one.trans (Real.one_le_rpow (mertensPrefixBudget_one_le (B j)) hr0)
    have hstepD : mertensPrefixBudget ((B j) ^ k) ≤
        D * (B j : ℝ) ^ ε * (mertensPrefixBudget (B j)) ^ r :=
      hj.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith)
          (Real.rpow_nonneg hBj0.le ε)) hEr0)
    have hlogs := Real.log_le_log (mertensPrefixBudget_pos _) hstepD
    rw [Real.log_mul (mul_ne_zero hD.ne' (Real.rpow_pos_of_pos hBj0 ε).ne')
        (Real.rpow_pos_of_pos (mertensPrefixBudget_pos _) r).ne',
      Real.log_mul hD.ne' (Real.rpow_pos_of_pos hBj0 ε).ne',
      Real.log_rpow hBj0, Real.log_rpow (mertensPrefixBudget_pos _)] at hlogs
    have hdivide := div_le_div_of_nonneg_right hlogs hlog.le
    have hnormalized :
        Real.log (mertensPrefixBudget ((B j) ^ k)) / Real.log (B j : ℝ) ≤
          Real.log D / Real.log (B j : ℝ) + ε +
          r * (Real.log (mertensPrefixBudget (B j)) / Real.log (B j : ℝ)) := by
      simpa only [add_div, mul_div_cancel_right₀ _ hlog.ne', mul_div_assoc] using hdivide
    linarith only [hnormalized]
  have hbound := le_of_tendsto hlimit hevent
  dsimp [ε] at hbound
  nlinarith only [hbound, mul_pos (sub_pos.mpr hrk) hh]

/-- The original full-prefix MU-LIFT criterion, with the permitted eventual
chain quantifier, is equivalent to critical Mertens growth. -/
theorem subcritical_prefixLiftOn_iff_mertens_half
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    MertensPrefixLiftOn B k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) :=
  ⟨mertens_half_of_subcritical_prefixLiftOn k hk r hr0 hrk B hB,
    fun hhalf => prefixLiftBound_on hB (prefixLiftBound_of_mertens_half k hk r hr0 hhalf)⟩

/-- The all-roots version has the same logical target. -/
theorem subcritical_prefixLiftBound_iff_mertens_half
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ)) :
    MertensPrefixLiftBound k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) := by
  constructor
  · intro h
    exact mertens_half_of_subcritical_prefixLiftOn k hk r hr0 hrk id tendsto_id
      (prefixLiftBound_on tendsto_id h)
  · exact prefixLiftBound_of_mertens_half k hk r hr0

/-- The paper route's explicit subpower gain supplies the chain proposition.
The gain and the full-prefix recurrence may both begin eventually. -/
theorem prefixLiftOn_of_subpower_gain
    {B : ℕ → ℕ} {G : ℕ → ℝ} {k : ℕ} {r : ℝ}
    (hB : Tendsto B atTop atTop)
    (hG : ∀ᶠ j : ℕ in atTop, 1 ≤ G j)
    (hlogG : Tendsto (fun j => Real.log (G j) / Real.log (B j : ℝ)) atTop (nhds 0))
    (hstep : ∀ᶠ j : ℕ in atTop,
      mertensPrefixBudget ((B j) ^ k) ≤ G j * (mertensPrefixBudget (B j)) ^ r) :
    MertensPrefixLiftOn B k r := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  have hnear := (tendsto_order.mp hlogG).2 ε hε
  filter_upwards [hnear, hG, hstep, hB.eventually (eventually_ge_atTop (2 : ℕ))]
    with j hjnear hjG hjstep hj2
  have hBj0 : (0 : ℝ) < (B j : ℝ) := by exact_mod_cast (show 0 < B j by omega)
  have hlog : 0 < Real.log (B j : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B j by omega))
  have hGj : 0 < G j := by linarith only [hjG]
  have hlogBound := (div_le_iff₀ hlog).mp hjnear.le
  have hgain : G j ≤ (B j : ℝ) ^ ε := by
    have h := (Real.log_le_iff_le_exp hGj).mp hlogBound
    rw [Real.rpow_def_of_pos hBj0]
    simpa only [mul_comm] using h
  simpa only [one_mul] using hjstep.trans
    (mul_le_mul_of_nonneg_right hgain
      (Real.rpow_nonneg (mertensPrefixBudget_nonneg _) r))

/-- Direct consumer of the original documented MU-LIFT subpower-gain format. -/
theorem mertens_half_of_subcritical_subpower_gain
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (G : ℕ → ℝ) (hB : Tendsto B atTop atTop)
    (hG : ∀ᶠ j : ℕ in atTop, 1 ≤ G j)
    (hlogG : Tendsto (fun j => Real.log (G j) / Real.log (B j : ℝ)) atTop (nhds 0))
    (hstep : ∀ᶠ j : ℕ in atTop,
      mertensPrefixBudget ((B j) ^ k) ≤ G j * (mertensPrefixBudget (B j)) ^ r) :
    MertensGrowthAtMost (1 / 2 : ℝ) :=
  mertens_half_of_subcritical_prefixLiftOn k hk r hr0 hrk B hB
    (prefixLiftOn_of_subpower_gain hB hG hlogG hstep)

/-- The documented MU-LIFT gain exists on the original unbounded chain:
it is eventually at least one, has zero logarithmic exponent, and controls
the full-prefix endpoint with the fixed budget power r. -/
def MertensPrefixSubpowerGainLiftOn (B : ℕ → ℕ) (k : ℕ) (r : ℝ) : Prop :=
  ∃ G : ℕ → ℝ,
    (∀ᶠ j : ℕ in atTop, 1 ≤ G j) ∧
    Tendsto (fun j => Real.log (G j) / Real.log (B j : ℝ)) atTop (nhds 0) ∧
    ∀ᶠ j : ℕ in atTop,
      mertensPrefixBudget ((B j) ^ k) ≤ G j * (mertensPrefixBudget (B j)) ^ r

/-- Exact equivalence for the original existential subpower-gain format,
including its permitted eventual unbounded-chain quantifier. -/
theorem subcritical_subpower_gain_iff_mertens_half
    (k : ℕ) (hk : 1 ≤ k) (r : ℝ) (hr0 : 0 ≤ r) (hrk : r < (k : ℝ))
    (B : ℕ → ℕ) (hB : Tendsto B atTop atTop) :
    MertensPrefixSubpowerGainLiftOn B k r ↔ MertensGrowthAtMost (1 / 2 : ℝ) := by
  constructor
  · rintro ⟨G, hG, hlogG, hstep⟩
    exact mertens_half_of_subcritical_subpower_gain k hk r hr0 hrk B G hB hG hlogG hstep
  · intro hhalf
    have hh := envelopeExponent_eq_zero_iff_mertens_half.mpr hhalf
    refine ⟨fun j => mertensPrefixBudget ((B j) ^ k), ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall
        (fun j => mertensPrefixBudget_one_le ((B j) ^ k))
    · simpa only [Function.comp_apply, hh, mul_zero] using
        (prefixBudget_power_log_ratio_tendsto k hk).comp hB
    · exact Filter.Eventually.of_forall (fun j =>
        le_mul_of_one_le_right (mertensPrefixBudget_nonneg ((B j) ^ k))
          (Real.one_le_rpow (mertensPrefixBudget_one_le (B j)) hr0))

end RHLean.Analysis.UniversalEnvelope

end
