import «research.MERTENS_EXPONENT_LOG_LIMSUP»

/-! Acceptance imports the original arithmetic carrier and the complete forward
analytic proof. There is no assumed converse or exponent-to-zero equivalence. -/

open RHLean.Analysis
open RHLean.Analysis.MertensExponent

example (n : ℕ) : ‖mertensSummatory n‖ ≤ (n : ℝ) := mertens_norm_le n
example : MertensPowerBound 1 := powerBound_one
example : 0 ≤ mertensGrowthExponent ∧ mertensGrowthExponent ≤ 1 :=
  ⟨growthExponent_nonneg, growthExponent_le_one⟩
example : mertensSummatory 5 = (-2 : ℂ) := mertens_five
example : ¬ (∀ n : ℕ, 1 ≤ n → ‖mertensSummatory n‖ ≤ Real.rpow (n : ℝ) 0) :=
  unit_horizontal_envelope_fails
example {a : ℝ} (ha : 0 ≤ a) (hM : MertensGrowthAtMost a)
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) : 1 - a ≤ ρ.re ∧ ρ.re ≤ a :=
  strip_of_growthAtMost ha hM ρ hρ
example {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    1 - mertensGrowthExponent ≤ ρ.re ∧ ρ.re ≤ mertensGrowthExponent :=
  strip_at_growthExponent ρ hρ
example (hM : MertensGrowthAtMost ((7 : ℝ) / 8))
    {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    (1 : ℝ) / 8 ≤ ρ.re ∧ ρ.re ≤ (7 : ℝ) / 8 := sevenEighths_strip hM hρ
example {ρ : ℂ} (hρ : NontrivialZetaZero ρ)
    (hleft : ρ.re = (1 : ℝ) / 16) :
    ¬ MertensPowerBound ((7 : ℝ) / 8) := by
  apply not_powerBound_of_zero_left (by norm_num) hρ
  rw [hleft]
  norm_num
example {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    ¬ MertensGrowthAtMost ((1 : ℝ) / 4) := by
  intro hM
  have hs := strip_of_growthAtMost (by norm_num : (0 : ℝ) ≤ 1 / 4) hM ρ hρ
  linarith [hs.1, hs.2]
example : ¬ MertensGrowthAtMost ((7 : ℝ) / 8) ↔
    ∃ ε : ℝ, 0 < ε ∧ ¬ MertensPowerBound ((7 : ℝ) / 8 + ε) :=
  not_growthAtMost_iff _
example (hne : ∃ ρ : ℂ, NontrivialZetaZero ρ) :
    zetaRightmostRealPart ≤ mertensGrowthExponent := rightmost_le_growthExponent hne
example (a : ℝ) (hne : ∃ ρ : ℂ, NontrivialZetaZero ρ) :
    ZerosInSymmetricStrip a ↔ zetaRightmostRealPart ≤ a := strip_iff_rightmost_le a hne
example : Filter.limsup mertensLogSlope Filter.atTop = mertensGrowthExponent :=
  logLimsup_eq_growthExponent
example {ρ : ℂ} (hρ : NontrivialZetaZero ρ) :
    1 - Filter.limsup mertensLogSlope Filter.atTop ≤ ρ.re ∧
    ρ.re ≤ Filter.limsup mertensLogSlope Filter.atTop := strip_at_logLimsup ρ hρ

#print axioms RHLean.Analysis.MertensExponent.mertens_norm_le
#print axioms RHLean.Analysis.MertensExponent.powerBound_one
#print axioms RHLean.Analysis.MertensExponent.powerBound_mono
#print axioms RHLean.Analysis.MertensExponent.growthAtMost_iff_growthExponent_le
#print axioms RHLean.Analysis.MertensExponent.mellin_eq_moebius_LSeries
#print axioms RHLean.Analysis.MertensExponent.reciprocal_identity_of_powerBound
#print axioms RHLean.Analysis.MertensExponent.zeta_ne_zero_of_powerBound
#print axioms RHLean.Analysis.MertensExponent.nontrivialZero_one_sub
#print axioms RHLean.Analysis.MertensExponent.strip_of_powerBound
#print axioms RHLean.Analysis.MertensExponent.strip_at_growthExponent
#print axioms RHLean.Analysis.MertensExponent.strip_of_growthAtMost
#print axioms RHLean.Analysis.MertensExponent.not_powerBound_of_zero_left
#print axioms RHLean.Analysis.MertensExponent.not_growthAtMost_of_zero_outside
#print axioms RHLean.Analysis.MertensExponent.half_le_growthExponent_of_zero
#print axioms RHLean.Analysis.MertensExponent.criticalLine_of_growth_half
#print axioms RHLean.Analysis.MertensExponent.sevenEighths_strip
#print axioms RHLean.Analysis.MertensExponent.mertens_five
#print axioms RHLean.Analysis.MertensExponent.unit_horizontal_envelope_fails
#print axioms RHLean.Analysis.MertensExponent.finite_prefix_constant_envelope
#print axioms RHLean.Analysis.MertensExponent.zero_re_le_rightmost
#print axioms RHLean.Analysis.MertensExponent.rightmost_le_growthExponent
#print axioms RHLean.Analysis.MertensExponent.strip_iff_rightmost_le
#print axioms RHLean.Analysis.MertensExponent.logLimsup_eq_growthExponent
#print axioms RHLean.Analysis.MertensExponent.strip_at_logLimsup
