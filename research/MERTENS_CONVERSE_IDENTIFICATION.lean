import «research.MERTENS_CONVERSE_INVERSION»
import PrimeNumberTheoremAnd.SmoothExistence

/-!
# Bidirectional identification of Mertens growth and zeta-zero confinement

The reverse theorem is proved by a constructed smoothing function, the proved
interior reciprocal estimate, a proved contour shift and the original finite
Mobius unsmoothing bound. The final equality compares the two independently
defined arithmetic and zero-coordinate extrema from the forward development.
No converse criterion, reciprocal estimate, inversion estimate or zero-existence
claim is supplied as an extra theorem hypothesis.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology ArithmeticFunction.Moebius BigOperators

/-- The existing sharp real cutoff is exactly the original complex Mertens sum
at every natural endpoint. This is an equality of the actual Mobius sums. -/
theorem sharpReal_nat_eq_mertens (n : ℕ) :
    (nativeMertensSharpReal (n : ℝ) : ℂ) = mertensSummatory n := by
  rw [← sum_Icc_one_moebius_eq_mertensSummatory]
  simp only [nativeMertensSharpReal, Nat.floor_natCast]
  push_cast
  rfl

/-- Unsmoothing with epsilon=4/X costs only a fixed constant. The independently
proved contour bound then gives a genuine global Mertens power envelope. -/
theorem powerBound_of_strip_interior
    {a σ q : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (hstrip : ZerosInSymmetricStrip a) (hq : 0 < q) (hq1 : q ≤ 1) :
    MertensPowerBound (σ + q) := by
  obtain ⟨ν, hνdiff, hνnonneg, hsupp, hνmass⟩ := SmoothExistence
  have hdiff : ContDiff ℝ 1 ν := hνdiff.of_le (by simp)
  have hnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ => hνnonneg x
  have hmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1 := by
    simpa only [integral_Ici_eq_integral_Ioi] using! hνmass
  obtain ⟨Cm, hCm, hsmoothed⟩ := smoothedMobius_bound_of_strip
    ha haσ hσ hstrip hq hq1 hdiff hsupp hnonneg hmass
  obtain ⟨Ce, hCe, hclose⟩ := strongMertens_smoothed_close_eps
    hdiff hsupp hnonneg hmass
  let B : ℝ := Cm * (4 : ℝ) ^ (-q) + 4 * Ce + 4
  have hfourPower : 0 ≤ (4 : ℝ) ^ (-q) := Real.rpow_nonneg (by norm_num) _
  have hB4 : 4 ≤ B := by
    have hterm := mul_nonneg hCm.le hfourPower
    dsimp [B]
    linarith
  have hB : 0 ≤ B := by linarith
  have hexponent : 0 ≤ σ + q := by linarith
  refine ⟨B, hB, ?_⟩
  intro n hn
  let X : ℝ := n
  have hX1 : 1 ≤ X := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hX : 0 < X := zero_lt_one.trans_le hX1
  have hXp : 1 ≤ X ^ (σ + q) := Real.one_le_rpow hX1 hexponent
  have hXp0 : 0 ≤ X ^ (σ + q) := Real.rpow_nonneg hX.le _
  by_cases hlarge : 4 < X
  · have hX3 : 3 < X := by linarith
    have hε : 0 < 4 / X := div_pos (by norm_num) hX
    have hε1 : 4 / X < 1 := (div_lt_one hX).mpr hlarge
    have hεX : (4 / X) * X = 4 := div_mul_cancel₀ 4 hX.ne'
    have hXε : 2 < X * (4 / X) := by rw [mul_comm, hεX]; norm_num
    have hsm := hsmoothed (4 / X) X hε hε1 hX3
    have hcl := hclose X hX3 (4 / X) hε hε1 hXε
    have hsharp : (nativeMertensSharpReal X : ℂ) = mertensSummatory n :=
      sharpReal_nat_eq_mertens n
    rw [hsharp, mul_assoc, hεX, mul_comm Ce 4] at hcl
    have hpowers : (4 / X) ^ (-q) * X ^ σ =
        (4 : ℝ) ^ (-q) * X ^ (σ + q) := by
      rw [Real.div_rpow (by norm_num) hX.le,
        Real.rpow_neg hX.le, div_inv_eq_mul, mul_assoc, ← Real.rpow_add hX]
      rw [add_comm q σ]
    have hsm' : ‖nativeSmoothedMobius ν (4 / X) X‖ ≤
        (Cm * (4 : ℝ) ^ (-q)) * X ^ (σ + q) := by
      calc
        ‖nativeSmoothedMobius ν (4 / X) X‖ ≤ Cm * (4 / X) ^ (-q) * X ^ σ := hsm
        _ = (Cm * (4 : ℝ) ^ (-q)) * X ^ (σ + q) := by
          rw [mul_assoc, hpowers]
          ring
    calc
      ‖mertensSummatory n‖ ≤ ‖nativeSmoothedMobius ν (4 / X) X‖ +
          ‖nativeSmoothedMobius ν (4 / X) X - mertensSummatory n‖ :=
        norm_le_norm_add_norm_sub _ _
      _ ≤ (Cm * (4 : ℝ) ^ (-q)) * X ^ (σ + q) + 4 * Ce :=
        add_le_add hsm' hcl
      _ ≤ (Cm * (4 : ℝ) ^ (-q)) * X ^ (σ + q) + (4 * Ce) * X ^ (σ + q) :=
        add_le_add_right (le_mul_of_one_le_right (by positivity) hXp) _
      _ = (Cm * (4 : ℝ) ^ (-q) + 4 * Ce) * X ^ (σ + q) := by ring
      _ ≤ B * X ^ (σ + q) :=
        mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) hXp0
  · have hsmall : X ≤ 4 := le_of_not_gt hlarge
    exact ((mertens_norm_le n).trans hsmall).trans
      (hB4.trans (le_mul_of_one_le_right hB hXp))

/-- The missing reverse implication: zero confinement supplies every positive
exponent-loss Mertens envelope. There is no additional analytic hypothesis. -/
theorem growthAtMost_of_strip {a : ℝ} (ha : 0 ≤ a)
    (hstrip : ZerosInSymmetricStrip a) : MertensGrowthAtMost a := by
  intro ε hε
  by_cases ha1 : 1 ≤ a
  · exact powerBound_mono (by linarith) powerBound_one
  have halt : a < 1 := lt_of_not_ge ha1
  let d : ℝ := min (ε / 4) ((1 - a) / 4)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (div_pos hε (by norm_num))
      (div_pos (sub_pos.mpr halt) (by norm_num))
  have hdε : d ≤ ε / 4 := min_le_left _ _
  have hda : d ≤ (1 - a) / 4 := min_le_right _ _
  have hd1 : d ≤ 1 := by linarith
  have hσ : a + d < 1 := by linarith
  have hpower : MertensPowerBound ((a + d) + d) :=
    powerBound_of_strip_interior ha (by linarith) hσ hstrip hd hd1
  exact powerBound_mono (by linarith) hpower

/-- The full parameterized bidirectional map. The epsilon losses on the
arithmetic side correspond to closed zero-strip boundaries. -/
theorem growthAtMost_iff_strip {a : ℝ} (ha : 0 ≤ a) :
    MertensGrowthAtMost a ↔ ZerosInSymmetricStrip a :=
  ⟨strip_of_growthAtMost ha, growthAtMost_of_strip ha⟩

/-- The independently defined zero supremum is nonnegative, including the
formal empty-set convention. No existence assertion is smuggled into the map. -/
theorem rightmost_nonneg : 0 ≤ zetaRightmostRealPart := by
  apply Real.sSup_nonneg
  rintro x ⟨ρ, hρ, rfl⟩
  exact hρ.2.1.le

/-- Each actual zero and its reflection lie in the strip supplied by the
independent zero supremum; no attained supremum or zero-existence premise. -/
theorem strip_at_rightmost : ZerosInSymmetricStrip zetaRightmostRealPart := by
  intro ρ hρ
  have hr := zero_re_le_rightmost hρ
  have hl := zero_re_le_rightmost (nontrivialZero_one_sub hρ)
  simp only [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, hr⟩

/-- The reverse inequality between the independent extremal coordinates. -/
theorem growthExponent_le_rightmost : mertensGrowthExponent ≤ zetaRightmostRealPart :=
  (growthAtMost_iff_growthExponent_le rightmost_nonneg).mp
    (growthAtMost_of_strip rightmost_nonneg strip_at_rightmost)

/-- The forward inequality also holds without a nonempty-set premise because
the arithmetic growth exponent is nonnegative. -/
theorem rightmost_le_growthExponent_unconditional :
    zetaRightmostRealPart ≤ mertensGrowthExponent := by
  apply Real.sSup_le _ growthExponent_nonneg
  rintro x ⟨ρ, hρ, rfl⟩
  exact zero_re_le_growthExponent hρ

/-- Direct bidirectional identification of the independently defined Mertens
power-growth boundary and the independently defined rightmost-zero boundary. -/
theorem growthExponent_eq_rightmost : mertensGrowthExponent = zetaRightmostRealPart :=
  le_antisymm growthExponent_le_rightmost rightmost_le_growthExponent_unconditional

/-- The literal logarithmic-limsup coordinate equals the genuine zeta-zero
supremum. This is an unconditional identification, not a proof of RH. -/
theorem logLimsup_eq_rightmost :
    Filter.limsup mertensLogSlope atTop = zetaRightmostRealPart :=
  logLimsup_eq_growthExponent.trans growthExponent_eq_rightmost

/-- The direct map is equivalently an upper bound on either coordinate. -/
theorem growthAtMost_iff_rightmost_le {a : ℝ} (ha : 0 ≤ a) :
    MertensGrowthAtMost a ↔ zetaRightmostRealPart ≤ a := by
  rw [growthAtMost_iff_growthExponent_le ha, growthExponent_eq_rightmost]

/-- Closed symmetric confinement is exactly the independent rightmost-zero
upper bound, now without the earlier nonemptiness argument. -/
theorem strip_iff_rightmost_le_unconditional {a : ℝ} (ha : 0 ≤ a) :
    ZerosInSymmetricStrip a ↔ zetaRightmostRealPart ≤ a :=
  (growthAtMost_iff_strip ha).symm.trans (growthAtMost_iff_rightmost_le ha)

/-- Critical-line specialization of the complete map. -/
theorem growthAtMost_half_iff_criticalZeros :
    MertensGrowthAtMost ((1 : ℝ) / 2) ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → ρ.re = (1 : ℝ) / 2 := by
  rw [growthAtMost_iff_strip (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  constructor
  · intro h ρ hρ
    obtain ⟨hl, hr⟩ := h ρ hρ
    linarith
  · intro h ρ hρ
    rw [h ρ hρ]
    constructor <;> norm_num

/-- Seven-eighths specialization, with no unconditional seven-eighths result
asserted: the two conditions themselves are proved equivalent. -/
theorem growthAtMost_sevenEighths_iff_strip :
    MertensGrowthAtMost ((7 : ℝ) / 8) ↔
      ∀ ρ : ℂ, NontrivialZetaZero ρ → (1 : ℝ) / 8 ≤ ρ.re ∧ ρ.re ≤ (7 : ℝ) / 8 := by
  simpa only [ZerosInSymmetricStrip, show (1 : ℝ) - 7 / 8 = 1 / 8 by norm_num] using!
    growthAtMost_iff_strip (by norm_num : (0 : ℝ) ≤ 7 / 8)

end RHLean.Analysis.MertensExponent
