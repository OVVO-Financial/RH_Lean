import «research.MERTENS_EXPONENT_DIAGNOSTICS»

/-!
# The arithmetic infimum is the logarithmic Mertens growth exponent

This file identifies the independently defined envelope infimum with the
literal integer-scale logarithmic limsup from the user's proposed map.
Only the elementary bound `norm (M n) <= n` is used for this identification.
No zero information, probability model, or exponent bound below one is assumed.
-/

noncomputable section
namespace RHLean.Analysis.MertensExponent
open Filter Set

/-- Literal logarithmic slope. Values at 0 and 1 do not affect the limsup. -/
def mertensLogSlope (n : ℕ) : ℝ :=
  Real.log (max 1 ‖mertensSummatory n‖) / Real.log (n : ℝ)

private theorem logSlope_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ mertensLogSlope n := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  exact div_nonneg (Real.log_nonneg (le_max_left _ _)) (Real.log_pos hnR).le

/-- For n >= 2 the log-coordinate inequality is an exact unit-envelope test. -/
theorem logSlope_le_iff {n : ℕ} (hn : 2 ≤ n) {b : ℝ} :
    mertensLogSlope n ≤ b ↔ max 1 ‖mertensSummatory n‖ ≤ (n : ℝ) ^ b := by
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hnR
  have hm : (0 : ℝ) < max 1 ‖mertensSummatory n‖ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold mertensLogSlope
  rw [div_le_iff₀ (Real.log_pos hnR), ← Real.log_rpow hn0]
  exact Real.log_le_log_iff hm (Real.rpow_pos_of_pos hn0 b)

private theorem logSlope_le_one {n : ℕ} (hn : 2 ≤ n) :
    mertensLogSlope n ≤ 1 := by
  apply (logSlope_le_iff hn).mpr
  rw [Real.rpow_one]
  exact max_le (by exact_mod_cast (show 1 ≤ n by omega)) (mertens_norm_le n)

/-- Eventual upper bounds of the logarithmic slope; the limsup is their infimum. -/
def logSlopeUpperBounds : Set ℝ := {b | ∀ᶠ n in atTop, mertensLogSlope n ≤ b}

private theorem logUpperBound_nonneg {b : ℝ} (hb : b ∈ logSlopeUpperBounds) :
    0 ≤ b := by
  obtain ⟨n, hbn, hn⟩ := (hb.and (eventually_ge_atTop (2 : ℕ))).exists
  exact (logSlope_nonneg hn).trans hbn

private theorem logUpperBounds_nonempty : logSlopeUpperBounds.Nonempty := by
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  exact logSlope_le_one hn

private theorem logUpperBounds_bddBelow : BddBelow logSlopeUpperBounds :=
  ⟨0, fun _b hb => logUpperBound_nonneg hb⟩

/-- An arbitrary multiplicative constant disappears after any positive
exponent increase, since log(C)/log(n) tends to zero. -/
theorem eventually_logSlope_le_of_powerBound_lt {a b : ℝ}
    (ha : 0 ≤ a) (hM : MertensPowerBound a) (hab : a < b) :
    b ∈ logSlopeUpperBounds := by
  obtain ⟨C, _hC, hbound⟩ := hM
  let D : ℝ := max 1 C
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hCD : C ≤ D := le_max_right _ _
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop,
      Real.log D / (b - a) ≤ Real.log (n : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlarge] with n hn hlargeN
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hnR
  have hpow0 : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg hn0.le a
  have hpow1 : 1 ≤ (n : ℝ) ^ a := by
    simpa only [Real.rpow_zero] using! Real.rpow_le_rpow_of_exponent_le hnR.le ha
  have hprod1 : 1 ≤ D * (n : ℝ) ^ a := by
    simpa only [one_mul] using! mul_le_mul hD1 hpow1 zero_le_one hD0.le
  have hnorm : ‖mertensSummatory n‖ ≤ D * (n : ℝ) ^ a :=
    (hbound n hn1).trans (mul_le_mul_of_nonneg_right hCD hpow0)
  have hm : (0 : ℝ) < max 1 ‖mertensSummatory n‖ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog := Real.log_le_log hm (max_le hprod1 hnorm)
  rw [Real.log_mul hD0.ne' (Real.rpow_pos_of_pos hn0 a).ne', Real.log_rpow hn0] at hlog
  have hCsmall := (div_le_iff₀ (sub_pos.mpr hab)).mp hlargeN
  apply (div_le_iff₀ (Real.log_pos hnR)).mpr
  nlinarith

/-- An eventual unit envelope gives a global constant envelope after absorbing
the finite initial segment. -/
theorem powerBound_of_eventually_logSlope_le {b : ℝ}
    (hb : b ∈ logSlopeUpperBounds) : MertensPowerBound b := by
  have hb0 : 0 ≤ b := logUpperBound_nonneg hb
  have htail : ∀ᶠ n : ℕ in atTop, ‖mertensSummatory n‖ ≤ (n : ℝ) ^ b := by
    filter_upwards [hb, eventually_ge_atTop (2 : ℕ)] with n hbn hn
    exact (le_max_right _ _).trans ((logSlope_le_iff hn).mp hbn)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hC0 : 0 ≤ (N : ℝ) + 1 := by positivity
  have hC1 : 1 ≤ (N : ℝ) + 1 := by
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  refine ⟨(N : ℝ) + 1, hC0, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow0 : 0 ≤ (n : ℝ) ^ b := Real.rpow_nonneg (Nat.cast_nonneg n) b
  have hpow1 : 1 ≤ (n : ℝ) ^ b := by
    simpa only [Real.rpow_zero] using! Real.rpow_le_rpow_of_exponent_le hnR hb0
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (by
      simpa only [one_mul] using! mul_le_mul_of_nonneg_right hC1 hpow0)
  · have hnN : (n : ℝ) ≤ (N : ℝ) + 1 := by
      exact_mod_cast (show n ≤ N + 1 by omega)
    exact ((mertens_norm_le n).trans hnN).trans (by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left hpow1 hC0)

/-- Exact agreement with the user's logarithmic-limsup exponent on integers. -/
theorem logLimsup_eq_growthExponent :
    Filter.limsup mertensLogSlope atTop = mertensGrowthExponent := by
  change sInf logSlopeUpperBounds = mertensGrowthExponent
  apply le_antisymm
  · apply le_csInf admissibleExponents_nonempty
    intro a ha
    by_contra hnot
    have hlt : a < sInf logSlopeUpperBounds := lt_of_not_ge hnot
    let b : ℝ := (a + sInf logSlopeUpperBounds) / 2
    have hab : a < b := by dsimp [b]; linarith
    have hb : b ∈ logSlopeUpperBounds :=
      eventually_logSlope_le_of_powerBound_lt ha.1 ha.2 hab
    have hLb : sInf logSlopeUpperBounds ≤ b := csInf_le logUpperBounds_bddBelow hb
    dsimp [b] at hLb
    linarith
  · apply le_csInf logUpperBounds_nonempty
    intro b hb
    exact csInf_le admissibleExponents_bddBelow
      ⟨logUpperBound_nonneg hb, powerBound_of_eventually_logSlope_le hb⟩

/-- Direct zeta enclosure expressed in the literal logarithmic-limsup coordinate. -/
theorem strip_at_logLimsup :
    ZerosInSymmetricStrip (Filter.limsup mertensLogSlope atTop) := by
  rw [logLimsup_eq_growthExponent]
  exact strip_at_growthExponent

end RHLean.Analysis.MertensExponent
