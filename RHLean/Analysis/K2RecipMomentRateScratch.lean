import RHLean.Analysis.K2RecipMomentAbelIdentificationScratch

noncomputable section

open Filter Set Topology
open scoped ArithmeticFunction.Moebius

namespace RHLean.Analysis

/-- The order-two Abel increments remain absolutely summable after one extra
logarithm.  This is the quantitative tail input needed for
`k2r N * log N -> 0`. -/
theorem k2MertensAbelTerm_two_mul_log_summable :
    Summable (fun N : ℕ =>
      Real.log (N : ℝ) * k2MertensAbelTerm 2 N) := by
  obtain ⟨c, C, hc, _hC, hM⟩ := strongNativeMertensSubexp
  let g : ℕ → ℝ := fun N =>
    8 * C * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 2))
  have hbase : Summable (fun N : ℕ =>
      1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 2)) := by
    rw [← summable_nat_add_iff 3 (G := ℝ)]
    exact (k2LogHarmonicTail_summable (p := 2) (by norm_num)).congr fun n => by
      simp [k2LogHarmonicTail, one_div, mul_inv_rev]
  have hg : Summable g := hbase.mul_left (8 * C)
  have hpowNat :
      ∀ᶠ N : ℕ in atTop,
        strongMertensScale (N : ℝ) ^ 50 ≤
          Real.exp (c * strongMertensScale (N : ℝ)) :=
    tendsto_natCast_atTop_atTop.eventually
      (strongMertens_scale_pow_le_exp_eventually 50 hc)
  apply Summable.of_norm_bounded_eventually_nat hg
  filter_upwards [eventually_ge_atTop 3, hpowNat] with N hN hpow
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNposNat
  have hL : 1 < Real.log (N : ℝ) := logt_gt_one (by exact_mod_cast hN : (3 : ℝ) ≤ N)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  let r := strongMertensScale (N : ℝ)
  have hr50 : (Real.log (N : ℝ)) ^ 5 = r ^ 50 := by
    have hs := strongMertensScale_pow_ten (X := (N : ℝ)) hN1
    dsimp [r]
    rw [← hs]
    ring
  have hdecay5 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 ≤ 1 := by
    rw [hr50]
    calc
      Real.exp (-c * r) * r ^ 50
          ≤ Real.exp (-c * r) * Real.exp (c * r) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hdecay3 :
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 ≤
        1 / (Real.log (N : ℝ)) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hLpos 2)]
    calc
      Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3 *
          (Real.log (N : ℝ)) ^ 2
          = Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 5 := by ring
      _ ≤ 1 := hdecay5
  have hweight := k2LogRecipWeight_two_diff_abs_le N hN
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg hN1),
    k2MertensAbelTerm, abs_mul]
  calc
    Real.log (N : ℝ) *
        (|nativeMertensSummatory N| *
          |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)|)
      ≤ Real.log (N : ℝ) *
          ((C * (N : ℝ) * Real.exp (-c * r)) *
            |k2LogRecipWeight 2 N - k2LogRecipWeight 2 (N + 1)|) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right
          · simpa [r, strongMertensScale, one_div] using hM N hN
          · exact abs_nonneg _
        · exact (Real.log_nonneg hN1)
    _ ≤ Real.log (N : ℝ) *
          ((C * (N : ℝ) * Real.exp (-c * r)) *
            (8 * (Real.log (N : ℝ)) ^ 2 / (N : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left hweight
          positivity
        · exact Real.log_nonneg hN1
    _ = (8 * C / (N : ℝ)) *
          (Real.exp (-c * r) * (Real.log (N : ℝ)) ^ 3) := by
        field_simp [ne_of_gt hNpos]
        ring
    _ ≤ (8 * C / (N : ℝ)) *
          (1 / (Real.log (N : ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hdecay3
        positivity
    _ = g N := by
        dsimp [g]
        field_simp [ne_of_gt hNpos]

end RHLean.Analysis
