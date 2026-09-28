import «research.PRIME_DENSITY_LOG_TIGHTENING»

/-!
# Discrete logarithmic saving for the exact PNT-density model

The Li singleton weights are nonnegative and decreasing. Discrete summation by
parts transfers the uniform signed unit-tail bound through these weights.
This avoids replacing any integer floor by a continuous argument. The resulting
constant 4 is deliberately looser than the separate continuous-curvature
candidate 2+(y-1)/x; no uncompiled curvature or rounding theorem is invoked.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace RHLean.Analysis
open RHLean.Arithmetic RHLean.Proof

/-- The existing singleton Li density, before the complex cast. -/
def densityTightLiWeight (q : ℕ) : ℝ :=
  logarithmicIntegralFromTwo (q : ℝ) -
    logarithmicIntegralFromTwo ((q - 1 : ℕ) : ℝ)

private theorem densityTight_invLog_integrable
    {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
  exact ((Real.continuousAt_log (by linarith)).inv₀
    (ne_of_gt (Real.log_pos (by linarith)))).continuousWithinAt

/-- Original interval endpoints are retained exactly. -/
theorem densityTightLiWeight_eq_integral {q : ℕ} (hq : 3 ≤ q) :
    densityTightLiWeight q =
      ∫ t in ((q - 1 : ℕ) : ℝ)..(q : ℝ), (Real.log t)⁻¹ := by
  have ha : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by omega)
  have h := intervalIntegral.integral_add_adjacent_intervals
    (densityTight_invLog_integrable (a := 2) (by norm_num) ha)
    (densityTight_invLog_integrable ha hb)
  unfold densityTightLiWeight logarithmicIntegralFromTwo
  linarith

theorem densityTightLiWeight_nonneg {q : ℕ} (hq : 3 ≤ q) :
    0 ≤ densityTightLiWeight q := by
  rw [densityTightLiWeight_eq_integral hq]
  apply intervalIntegral.integral_nonneg
    (by exact_mod_cast Nat.sub_le q 1)
  intro t ht
  apply inv_nonneg.mpr
  apply Real.log_nonneg
  have ha : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ q - 1 by omega)
  linarith [ht.1]

/-- Exact monotonicity of consecutive Li singleton masses. -/
theorem densityTightLiWeight_antitone_step {q : ℕ} (hq : 3 ≤ q) :
    densityTightLiWeight (q + 1) ≤ densityTightLiWeight q := by
  rw [densityTightLiWeight_eq_integral (by omega), densityTightLiWeight_eq_integral hq]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have ha : (2 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ q - 1 by omega)
  have hb : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by omega)
  have hp : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by exact_mod_cast (show q - 1 + 1 = q by omega)
  have hab : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by linarith
  have hshift := intervalIntegral.integral_comp_add_right
    (a := ((q - 1 : ℕ) : ℝ)) (b := (q : ℝ))
    (fun t : ℝ => (Real.log t)⁻¹) 1
  rw [hp] at hshift
  rw [← hshift]
  have hfi : IntervalIntegrable (fun t : ℝ => (Real.log (t + 1))⁻¹)
      volume ((q - 1 : ℕ) : ℝ) (q : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := (le_min ha hb).trans ht.1
    exact (((continuousAt_id.add_const 1).log (by linarith)).inv₀
      (ne_of_gt (Real.log_pos (by linarith)))).continuousWithinAt
  apply intervalIntegral.integral_mono_on hab hfi (densityTight_invLog_integrable ha hb)
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := ha.trans ht.1
  have hlog : Real.log t ≤ Real.log (t + 1) := Real.log_le_log (by linarith) (by linarith)
  exact (inv_le_inv₀ (Real.log_pos (by linarith)) (Real.log_pos (by linarith))).2 hlog

/-- Abel invariant with the terminal endpoint still attached. -/
theorem densityTight_weighted_difference_invariant
    (d : ℕ → ℝ) (F : ℕ → ℂ) (y : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hd : ∀ q, y < q → 0 ≤ d q)
    (hanti : ∀ q, y < q → d (q + 1) ≤ d q)
    (hF : ∀ q, y ≤ q → ‖F q‖ ≤ B)
    (x : ℕ) (hyx : y < x) :
    ‖(∑ q ∈ Finset.Ioc y x, (d q : ℂ) * (F (q - 1) - F q)) +
        (d x : ℂ) * F x‖ ≤
      (2 * d (y + 1) - d x) * B := by
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases h : y < x
      · have hi := ih h
        have hid :
            (∑ q ∈ Finset.Ioc y (x + 1), (d q : ℂ) * (F (q - 1) - F q)) +
                (d (x + 1) : ℂ) * F (x + 1) =
              ((∑ q ∈ Finset.Ioc y x, (d q : ℂ) * (F (q - 1) - F q)) +
                (d x : ℂ) * F x) + ((d (x + 1) - d x : ℝ) : ℂ) * F x := by
          rw [Finset.sum_Ioc_succ_top h.le]
          simp only [Nat.add_sub_cancel, Complex.ofReal_sub]
          ring
        rw [hid]
        calc
          _ ≤ ‖(∑ q ∈ Finset.Ioc y x, (d q : ℂ) * (F (q - 1) - F q)) + (d x : ℂ) * F x‖ +
              ‖((d (x + 1) - d x : ℝ) : ℂ) * F x‖ := norm_add_le _ _
          _ ≤ (2 * d (y + 1) - d x) * B + (d x - d (x + 1)) * B := by
            apply add_le_add hi
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hanti x h)), neg_sub]
            exact mul_le_mul_of_nonneg_left (hF x h.le) (sub_nonneg.mpr (hanti x h))
          _ = (2 * d (y + 1) - d (x + 1)) * B := by ring
      · have heq : x = y := by omega
        subst x
        rw [Nat.Ioc_succ_singleton, Finset.sum_singleton]
        simp only [Nat.add_sub_cancel]
        have hid : (d (y + 1) : ℂ) * (F y - F (y + 1)) +
            (d (y + 1) : ℂ) * F (y + 1) = (d (y + 1) : ℂ) * F y := by ring
        rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hd (y + 1) (by omega))]
        calc
          _ ≤ d (y + 1) * B := mul_le_mul_of_nonneg_left (hF y le_rfl) (hd _ (by omega))
          _ = (2 * d (y + 1) - d (y + 1)) * B := by ring

/-- The unit-density tail's exact one-site difference. -/
theorem densityTight_unit_tail_difference {y x q : ℕ}
    (hq : q ∈ Finset.Ioc y x) :
    primeSieveUnitDensityBulk (q - 1) x - primeSieveUnitDensityBulk q x =
      mertensSummatory (x / q) := by
  have hqp : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqp)
  have hqx := (Finset.mem_Ioc.mp hq).2
  have h := Finset.sum_Ioc_consecutive (fun i => mertensSummatory (x / i))
    (Nat.le_succ k) hqx
  rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
  unfold primeSieveUnitDensityBulk
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h ⊢
  linear_combination -h

/-- Logarithmic saving for the exact discrete Li model. No floors are changed.
The constant 4 comes from the two-sided Abel boundary budget. -/
theorem norm_primeSievePNTBulk_le_four_div_log
    {y : ℕ} (hy : 2 ≤ y) (x : ℕ) :
    ‖primeSievePNTBulk y x‖ ≤ 4 * (x : ℝ) / Real.log (y : ℝ) := by
  have hl : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  by_cases hyx : y < x
  · let F : ℕ → ℂ := fun t => primeSieveUnitDensityBulk t x
    have hi := densityTight_weighted_difference_invariant densityTightLiWeight F y
      (B := 2 * (x : ℝ)) (by positivity)
      (fun q hq => densityTightLiWeight_nonneg (by omega))
      (fun q hq => densityTightLiWeight_antitone_step (by omega))
      (fun q _ => norm_primeSieveUnitDensityBulk_le_two_mul q x) x hyx
    have hFx : F x = 0 := by simp [F, primeSieveUnitDensityBulk]
    rw [hFx, mul_zero, add_zero] at hi
    have hsum : (∑ q ∈ Finset.Ioc y x,
        (densityTightLiWeight q : ℂ) * (F (q - 1) - F q)) = primeSievePNTBulk y x := by
      unfold primeSievePNTBulk
      apply Finset.sum_congr rfl
      intro q hq
      change (densityTightLiWeight q : ℂ) *
          (primeSieveUnitDensityBulk (q - 1) x - primeSieveUnitDensityBulk q x) = _
      rw [densityTight_unit_tail_difference hq]
      rfl
    rw [hsum] at hi
    have hdx : 0 ≤ densityTightLiWeight x := densityTightLiWeight_nonneg (by omega)
    have hc : densityTightLiWeight (y + 1) ≤ (Real.log (y : ℝ))⁻¹ := by
      have h := norm_primeSievePNTDensity_le_inv_log hy (Nat.lt_succ_self y)
      change ‖(densityTightLiWeight (y + 1) : ℂ)‖ ≤ _ at h
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (densityTightLiWeight_nonneg (by omega))] at h
      exact h
    have hxc : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
    calc
      _ ≤ (2 * densityTightLiWeight (y + 1) - densityTightLiWeight x) * (2 * (x : ℝ)) := hi
      _ ≤ 4 * (x : ℝ) * (Real.log (y : ℝ))⁻¹ := by nlinarith
      _ = 4 * (x : ℝ) / Real.log (y : ℝ) := by ring
  · unfold primeSievePNTBulk
    rw [Finset.Ioc_eq_empty_of_le (Nat.le_of_not_gt hyx)]
    simp only [Finset.sum_empty, norm_zero]
    positivity

/-- Preserve both the improved constant and the logarithmic saving. -/
theorem primeSievePNTBulk_energy_tight
    {y x : ℕ} (hy : 2 ≤ y) (hxy : x ≤ y ^ 2) :
    ‖primeSievePNTBulk y x‖ ^ 2 ≤
      min ((x : ℝ) ^ 2) (16 * (x : ℝ) ^ 2 / Real.log (y : ℝ) ^ 2) := by
  have ha := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTBulk_le_endpoint hy hxy)
  have hb := mul_self_le_mul_self (norm_nonneg _) (norm_primeSievePNTBulk_le_four_div_log hy x)
  apply le_min
  · nlinarith
  · convert hb using 1 <;> ring

/-- A logarithmically improved additive error envelope; the error is NOT dropped. -/
theorem norm_primeSievePNTError_le_log_envelope
    {y x : ℕ} (hy : 2 ≤ y) (hroot : Nat.sqrt x < y) :
    ‖primeSievePNTError y x‖ ≤ (x : ℝ) + 4 * (x : ℝ) / Real.log (y : ℝ) := by
  rw [primeSievePNTError_eq_tail_sub_bulk]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_primeSieveMertensPrimeTail_le_endpoint hroot)
    (norm_primeSievePNTBulk_le_four_div_log hy x))

/-- The initial model/error coefficient allocation reaches the 9/4 corridor
when its two displayed arithmetic premises are supplied. -/
theorem densityTight_signed_energy_budget_nine_quarters
    (a e D E L Cb Ce : ℝ)
    (hD : D ≤ 3 * L)
    (hb : a ^ 2 - D ≤ E + Cb * L)
    (he : e ^ 2 ≤ (1 / 4 : ℝ) * E + Ce * L) :
    (a - e) ^ 2 - D ≤ (9 / 4 : ℝ) * E +
      ((3 / 2 : ℝ) * Cb + 3 * Ce + 3 / 2) * L := by
  have h := densityTight_signed_energy_budget a e D E L 1 (1 / 4) Cb Ce (1 / 2)
    (by norm_num) hD (by simpa using hb) he
  norm_num at h ⊢
  nlinarith

end RHLean.Analysis
