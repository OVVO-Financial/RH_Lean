import «research.PRIME_DENSITY_PNT_LOG_BOUND»

/-!
# Integral-sensitive Li-density constant

Keep the actual Li singleton density inside the reciprocal integral rather
than freezing it. This gives |T_Li| <= x log 2 on every root-to-square tail.
Combined with the discrete Abel estimate it preserves both constant and rate
improvements. The exact prime-minus-Li error stays explicit throughout.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof

private theorem densityIntegral_mertens_norm_le (n : ℕ) :
    ‖mertensSummatory n‖ ≤ (n : ℝ) := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory n]
  unfold cofactorMobiusPrefixMass
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 n, ‖canonicalMoebiusWeight m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 n, (1 : ℝ) :=
      Finset.sum_le_sum fun m _ => norm_canonicalMoebiusWeight_le_one m
    _ = (n : ℝ) := by simp

private theorem densityIntegral_invLog_integrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  exact ((Real.continuousAt_log (by linarith)).inv₀
    (ne_of_gt (Real.log_pos (by linarith)))).continuousWithinAt

private theorem densityIntegral_loglog_integrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hc0 : ContinuousAt (fun s : ℝ => s * Real.log s) t :=
    continuousAt_id.mul (Real.continuousAt_log ht0)
  have hc1 : ContinuousAt (fun s : ℝ => 1 / (s * Real.log s)) t :=
    continuousAt_const.div hc0 (mul_ne_zero ht0 hl0)
  exact hc1.continuousWithinAt

private theorem densityIntegral_loglog_primitive
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∫ t in a..b, 1 / (t * Real.log t)) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => Real.log (Real.log t)) _
    (densityIntegral_loglog_integrable ha hb)
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  have ht0 : t ≠ 0 := by linarith
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  convert (Real.hasDerivAt_log ht0).log hl0 using 1 <;>
    simp only [one_div, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- One exact Li interval pays a log-log increment, not a frozen log density. -/
theorem densityTightLiWeight_div_le_loglog_step {q : ℕ} (hq : 3 ≤ q) :
    densityTightLiWeight q / (q : ℝ) ≤
      Real.log (Real.log (q : ℝ)) - Real.log (Real.log ((q - 1 : ℕ) : ℝ)) := by
  have ha : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by omega)
  have hab : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
  rw [densityTightLiWeight_eq_integral hq, ← intervalIntegral.integral_div]
  calc
    _ ≤ ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ), 1 / (t * Real.log t) := by
      apply intervalIntegral.integral_mono_on hab
        ((densityIntegral_invLog_integrable ha hb).div_const (q : ℝ))
        (densityIntegral_loglog_integrable ha hb)
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ha.trans ht.1
      have hl : 0 ≤ (Real.log t)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by linarith))
      calc
        (Real.log t)⁻¹ / (q : ℝ) ≤ (Real.log t)⁻¹ / t :=
          div_le_div_of_nonneg_left hl (by linarith) ht.2
        _ = 1 / (t * Real.log t) := by simp only [one_div, div_eq_mul_inv, mul_inv_rev]
    _ = _ := densityIntegral_loglog_primitive ha hb

private theorem densityIntegral_sum_backward_difference
    (f : ℕ → ℝ) {y x : ℕ} (hyx : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x, (f q - f (q - 1))) = f x - f y := by
  induction x with
  | zero => have hy : y = 0 := by omega; subst y; simp
  | succ x ih =>
      by_cases h : y ≤ x
      · rw [Finset.sum_Ioc_succ_top h, ih h]
        simp only [Nat.add_sub_cancel]
        ring
      · have heq : y = x + 1 := by omega
        subst y
        simp

/-- The exact Li reciprocal mass telescopes to log-log endpoint differences. -/
theorem densityTightLi_reciprocal_mass_le
    {y x : ℕ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    (∑ q ∈ Finset.Ioc y x, densityTightLiWeight q / (q : ℝ)) ≤
      Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc y x,
        (Real.log (Real.log (q : ℝ)) - Real.log (Real.log ((q - 1 : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact densityTightLiWeight_div_le_loglog_step (by have := (Finset.mem_Ioc.mp hq).1; omega)
    _ = _ := densityIntegral_sum_backward_difference (fun q => Real.log (Real.log (q : ℝ))) hyx

/-- Improved universal Li amplitude constant: log(2), with no assumed PNT error. -/
theorem norm_primeSievePNTBulk_le_log_two_mul
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ≤ Real.log 2 * (x : ℝ) := by
  by_cases hyx : y ≤ x
  · have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hly : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have hlx : 0 < Real.log (x : ℝ) := hly.trans_le (Real.log_le_log hypos (by exact_mod_cast hyx))
    have hxlog : Real.log (x : ℝ) ≤ 2 * Real.log (y : ℝ) := by
      calc
        Real.log (x : ℝ) ≤ Real.log ((y : ℝ) ^ 2) := Real.log_le_log hxpos (by exact_mod_cast hxy)
        _ = 2 * Real.log (y : ℝ) := by rw [Real.log_pow]; norm_num
    have hll := Real.log_le_log hlx hxlog
    rw [Real.log_mul (by norm_num) (ne_of_gt hly)] at hll
    have hmass := densityTightLi_reciprocal_mass_le hy hyx
    have hm : (∑ q ∈ Finset.Ioc y x, densityTightLiWeight q / (q : ℝ)) ≤ Real.log 2 := by linarith
    unfold primeSievePNTBulk
    calc
      _ ≤ ∑ q ∈ Finset.Ioc y x, ‖primeSievePNTDensity q * mertensSummatory (x / q)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Finset.Ioc y x, (x : ℝ) * (densityTightLiWeight q / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hq3 : 3 ≤ q := by have := (Finset.mem_Ioc.mp hq).1; omega
        have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hn : 0 ≤ densityTightLiWeight q := densityTightLiWeight_nonneg hq3
        have hdiv : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) := by
          apply (le_div_iff₀ hqr).mpr
          exact_mod_cast Nat.div_mul_le_self x q
        change ‖(densityTightLiWeight q : ℂ) * mertensSummatory (x / q)‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
        have h := mul_le_mul_of_nonneg_left ((densityIntegral_mertens_norm_le (x / q)).trans hdiv) hn
        convert h using 1 <;> ring
      _ = (x : ℝ) * ∑ q ∈ Finset.Ioc y x, densityTightLiWeight q / (q : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ (x : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg x)
      _ = Real.log 2 * (x : ℝ) := mul_comm _ _
  · unfold primeSievePNTBulk
    rw [Finset.Ioc_eq_empty_of_le (Nat.le_of_not_ge hyx)]
    simp only [Finset.sum_empty, norm_zero]
    positivity

/-- The strongest compiled combination of the integral constant and discrete rate. -/
theorem primeSievePNTBulk_energy_integral_tight
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ^ 2 ≤ min
      (Real.log 2 ^ 2 * (x : ℝ) ^ 2)
      (16 * (x : ℝ) ^ 2 / Real.log (y : ℝ) ^ 2) := by
  have ha := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTBulk_le_log_two_mul hy hxy)
  have hb := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTBulk_le_four_div_log hy x)
  apply le_min
  · nlinarith
  · convert hb using 1 <;> ring

/-- Actual prime-minus-Li error, with the sharper integral constant. -/
theorem norm_primeSievePNTError_le_one_add_log_two
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) (hroot : Nat.sqrt x < y) :
    ‖primeSievePNTError y x‖ ≤ (1 + Real.log 2) * (x : ℝ) := by
  rw [primeSievePNTError_eq_tail_sub_bulk]
  have h := (norm_sub_le (primeSieveMertensPrimeTail y x) (primeSievePNTBulk y x)).trans
    (add_le_add (norm_primeSieveMertensPrimeTail_le_endpoint hroot)
      (norm_primeSievePNTBulk_le_log_two_mul hy hxy))
  nlinarith

end RHLean.Analysis
