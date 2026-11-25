import RHLean.Analysis.AlpogeNativeSubgroupProjection
import RHLean.Analysis.AlpogeThin.NativeDyadicHostPrimePowerWeights
import RHLean.Analysis.AlpogeThin.NativeDyadicHostRaw

/-! The selected discriminant prime pays its complete contribution on the
outer window. The widths, top set, lift indices, cutoff, and projection
divisor are those of the original native arithmetic source. -/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis.AlpogeThin

/-- Normalize every power of the ramified prime of the same window pair.
The first inequality retains the measured density; the second charges the
density to the original power allowance. -/
theorem nativeDyadicDPrimeASK_normalized_le_of_winPair
    {ι : Type*} (e q d N : ℕ) {ε Y x b : ℝ} (hε : 0 < ε)
    (hY : Real.exp 16 ≤ Y) (hx : 1 ≤ x) (hhi : x ≤ Y ^ (2 : ℕ))
    (hpair : UpperTheory.Top.WinPair ε Y q d)
    (J : Finset ι) (T T2 : Finset (AlpogeNativeDyadicH e))
    (hJ : J.Nonempty) (hT : T.Nonempty) (hb : 0 < b)
    (hdensity : x ^ (-ε) ≤ alpogeNativeProjectionDensity T2)
    (a : AlpogeNativeDyadicH e → ℝ)
    (w : ι → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℝ)
    (ha : ∀ t ∈ T, 0 ≤ a t ∧ a t ≤ b * (x + 1))
    (hw : ∀ j ∈ J, ∀ ρ, alpogeNativeInPhi ρ → 0 ≤ w j ρ) :
    letI : Fact q.Prime := ⟨hpair.q_prime⟩
    letI : Fact d.Prime := ⟨hpair.d_prime⟩
    let Z := ‖∑ j ∈ J, ∑ t ∈ T, nativeDyadicDPrimeASK e q d N (a t) t (w j)‖ /
      alpogeNativeProjectionDivisor T T2 J.card b
    Z ≤ 16 / (alpogeNativeProjectionDensity T2 * x) ∧ Z ≤ 16 * x ^ (ε - 1) := by
  letI : Fact q.Prime := ⟨hpair.q_prime⟩
  letI : Fact d.Prime := ⟨hpair.d_prime⟩
  let Δ := alpogeNativeProjectionDensity T2
  let Z := ‖∑ j ∈ J, ∑ t ∈ T, nativeDyadicDPrimeASK e q d N (a t) t (w j)‖ /
    alpogeNativeProjectionDivisor T T2 J.card b
  change Z ≤ 16 / (Δ * x) ∧ Z ≤ 16 * x ^ (ε - 1)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hΔ : 0 < Δ := (Real.rpow_pos_of_pos hx0 (-ε)).trans_le hdensity
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 16)).trans hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hlogY : 16 ≤ Real.log Y := by
    simpa only [Real.log_exp] using (Real.log_le_log (Real.exp_pos 16) hY)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hpair.d_prime.two_le
  have hd0 : (0 : ℝ) < d := by linarith
  have hm : Real.log Y ^ 2 ≤ Y ^ (ε / 5) * Real.log Y ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow hY1 (by positivity))
  have hlog8 : 8 * Real.log Y ≤ Real.log d := by
    nlinarith only [hpair.d_lo, hm,
      mul_nonneg (Real.log_nonneg hY1) (sub_nonneg.mpr hlogY)]
  have hY8 : Y ^ (8 : ℕ) ≤ (d : ℝ) := by
    apply (Real.log_le_log_iff (pow_pos hY0 _) hd0).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog8
  have hs : x ^ (2 : ℕ) ≤ Real.sqrt (d : ℝ) := by
    apply (sq_le_sq₀ (sq_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hd0.le]
    calc
      (x ^ (2 : ℕ)) ^ (2 : ℕ) = x ^ (4 : ℕ) := by ring
      _ ≤ (Y ^ (2 : ℕ)) ^ (4 : ℕ) := pow_le_pow_left₀ hx0.le hhi _
      _ = Y ^ (8 : ℕ) := by ring
      _ ≤ _ := hY8
  have hld : Real.log (d : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
    have h := Real.log_le_rpow_div hd0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith only [h]
  have hnum : 2 * (x + 1) * Real.log d * x ≤ 16 * ((d : ℝ) - 1) := by
    calc
      _ ≤ 2 * (2 * x) * (2 * Real.sqrt (d : ℝ)) * x := by
        apply mul_le_mul_of_nonneg_right _ hx0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : x + 1 ≤ 2 * x)
          (by norm_num : (0 : ℝ) ≤ 2)) hld (Real.log_natCast_nonneg d) (by positivity)
      _ = 8 * (x ^ (2 : ℕ) * Real.sqrt (d : ℝ)) := by ring
      _ ≤ 8 * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by norm_num)
      _ ≤ _ := by rw [Real.mul_self_sqrt hd0.le]; linarith only [hd2]
  have hZ : Z ≤ 16 / (Δ * x) := by
    apply (nativeDyadicDPrimeASK_normalized_le e q d N (nativeDyadicHostHyp_of_winPair hpair)
      J T hJ hT a w x b Δ hb hΔ ha hw).trans
    apply (div_le_div_iff₀ (mul_pos hΔ (by linarith : 0 < (d : ℝ) - 1)) (mul_pos hΔ hx0)).mpr
    calc
      2 * (x + 1) * Real.log d * (Δ * x) = Δ * (2 * (x + 1) * Real.log d * x) := by ring
      _ ≤ Δ * (16 * ((d : ℝ) - 1)) := mul_le_mul_of_nonneg_left hnum hΔ.le
      _ = 16 * (Δ * ((d : ℝ) - 1)) := by ring
  refine ⟨hZ, hZ.trans ((div_le_iff₀ (mul_pos hΔ hx0)).mpr ?_)⟩
  have hinv : (x ^ (-ε) * x) * x ^ (ε - 1) = 1 := by
    calc
      _ = (x ^ (-ε) * x ^ (1 : ℝ)) * x ^ (ε - 1) := by rw [Real.rpow_one]
      _ = 1 := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, show -ε + 1 + (ε - 1) = 0 by ring,
          Real.rpow_zero]
  have hpaid : 1 ≤ (Δ * x) * x ^ (ε - 1) := by
    exact hinv.symm.le.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdensity hx0.le) (Real.rpow_nonneg hx0.le _))
  calc
    16 = 16 * (1 : ℝ) := by ring
    _ ≤ 16 * (Δ * x * x ^ (ε - 1)) := mul_le_mul_of_nonneg_left hpaid (by norm_num)
    _ = 16 * x ^ (ε - 1) * (Δ * x) := by ring

end RHLean.Analysis.AlpogeThin

end
