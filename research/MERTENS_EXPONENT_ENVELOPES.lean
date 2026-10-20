import RHLean.Analysis.MertensMellinLSeriesBridge

/-!
# Genuine Mertens power envelopes

All bounds refer to the existing `mertensSummatory`, not a model sequence.
`MertensPowerBound a` permits a constant C and includes every positive integer.
`MertensGrowthAtMost a` permits an arbitrarily small positive exponent loss.
The growth exponent is independently defined as an infimum of admissible
nonnegative exponents. No zeta-zero information enters its definition.

A unit-envelope crossing is not the negation of a power bound with arbitrary C.
The analytic reverse implication from a zero-free strip is not assumed here.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Filter Asymptotics Set
open scoped ArithmeticFunction.Moebius BigOperators

/-- A global power envelope, with its multiplicative constant quantified. -/
def MertensPowerBound (a : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    ‖mertensSummatory n‖ ≤ C * Real.rpow (n : ℝ) a

/-- Exponent-level control; no assertion at the exact boundary is implicit. -/
def MertensGrowthAtMost (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → MertensPowerBound (a + ε)

/-- The linear cone is an unconditional arithmetic theorem. -/
theorem mertens_norm_le (n : ℕ) : ‖mertensSummatory n‖ ≤ (n : ℝ) := by
  rw [← sum_Icc_one_moebius_eq_mertensSummatory]
  calc
    ‖∑ k ∈ Finset.Icc 1 n, ((μ k : ℤ) : ℂ)‖ ≤
        ∑ k ∈ Finset.Icc 1 n, ‖((μ k : ℤ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
    _ = (n : ℝ) := by simp

/-- The exponent-one bound holds with C = 1, not merely on a finite census. -/
theorem powerBound_one : MertensPowerBound 1 := by
  refine ⟨1, zero_le_one, fun n _hn => ?_⟩
  simpa using! mertens_norm_le n

/-- Enlarging an exponent preserves an admissible envelope. -/
theorem powerBound_mono {a b : ℝ} (hab : a ≤ b)
    (h : MertensPowerBound a) : MertensPowerBound b := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact (hbound n hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hnR hab) hC)

/-- An exact power bound implies exponent-level control. -/
theorem growthAtMost_of_powerBound {a : ℝ} (h : MertensPowerBound a) :
    MertensGrowthAtMost a := by
  intro ε hε
  exact powerBound_mono (by linarith) h

/-- Exponent-level control is monotone. -/
theorem growthAtMost_mono {a b : ℝ} (hab : a ≤ b)
    (h : MertensGrowthAtMost a) : MertensGrowthAtMost b := by
  intro ε hε
  exact powerBound_mono (by linarith) (h ε hε)

/-- Natural-number Landau form of a global envelope. -/
theorem powerBound_isBigO {a : ℝ} (h : MertensPowerBound a) :
    (fun n : ℕ => mertensSummatory n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  obtain ⟨C, _hC, hbound⟩ := h
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)]
  exact hbound n hn

/-- Transfer the genuine integer envelope to the actual floor-step function. -/
theorem powerBound_step_isBigO {a : ℝ} (ha : 0 ≤ a)
    (h : MertensPowerBound a) :
    mertensStep =O[atTop] (fun t : ℝ => t ^ a) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := by linarith
  rw [mertensStep_eq_mertensSummatory_floor,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 a)]
  by_cases hf : ⌊t⌋₊ = 0
  · rw [hf, mertensSummatory_zero, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg ht0 a)
  · have hf1 : 1 ≤ ⌊t⌋₊ := by omega
    exact (hbound ⌊t⌋₊ hf1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0) ha) hC)

/-- Admissibility is defined arithmetically, independently of the zeta zeros. -/
def admissibleExponents : Set ℝ := {a | 0 ≤ a ∧ MertensPowerBound a}

/-- Infimum convention avoids asserting boundedness at the boundary exponent. -/
def mertensGrowthExponent : ℝ := sInf admissibleExponents

theorem admissibleExponents_nonempty : admissibleExponents.Nonempty :=
  ⟨1, zero_le_one, powerBound_one⟩

theorem admissibleExponents_bddBelow : BddBelow admissibleExponents :=
  ⟨0, fun _a ha => ha.1⟩

theorem growthExponent_nonneg : 0 ≤ mertensGrowthExponent := by
  exact le_csInf admissibleExponents_nonempty (fun _a ha => ha.1)

theorem growthExponent_le_one : mertensGrowthExponent ≤ 1 := by
  exact csInf_le admissibleExponents_bddBelow ⟨zero_le_one, powerBound_one⟩

/-- Every exponent strictly above the infimum has a genuine global envelope. -/
theorem powerBound_of_growthExponent_lt {a : ℝ}
    (ha : mertensGrowthExponent < a) : MertensPowerBound a := by
  have hex : ∃ b ∈ admissibleExponents, b < a := by
    by_contra hnot
    push Not at hnot
    have hle : a ≤ mertensGrowthExponent :=
      le_csInf admissibleExponents_nonempty hnot
    exact (not_le_of_gt ha) hle
  obtain ⟨b, hb, hba⟩ := hex
  exact powerBound_mono hba.le hb.2

/-- The infimum definition is exactly equivalent to epsilon-loss growth. -/
theorem growthAtMost_iff_growthExponent_le {a : ℝ} (ha : 0 ≤ a) :
    MertensGrowthAtMost a ↔ mertensGrowthExponent ≤ a := by
  constructor
  · intro h
    by_contra hnot
    have hlt : a < mertensGrowthExponent := lt_of_not_ge hnot
    let ε := (mertensGrowthExponent - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hmem : a + ε ∈ admissibleExponents := ⟨by linarith, h ε hε⟩
    have hle : mertensGrowthExponent ≤ a + ε :=
      csInf_le admissibleExponents_bddBelow hmem
    dsimp [ε] at hle
    linarith
  · intro h ε hε
    apply powerBound_of_growthExponent_lt
    linarith

/-- Negation uses SOME positive exponent gap, not every positive epsilon. -/
theorem not_growthAtMost_iff (a : ℝ) :
    ¬ MertensGrowthAtMost a ↔
      ∃ ε : ℝ, 0 < ε ∧ ¬ MertensPowerBound (a + ε) := by
  simp only [MertensGrowthAtMost, not_forall, exists_prop]

/-- A certified finite crossing disproves only the specified constant. -/
theorem fixed_envelope_fails_of_witness {a C : ℝ} {n : ℕ}
    (hn : 1 ≤ n)
    (hcross : C * Real.rpow (n : ℝ) a < ‖mertensSummatory n‖) :
    ¬ (∀ k : ℕ, 1 ≤ k →
      ‖mertensSummatory k‖ ≤ C * Real.rpow (k : ℝ) a) := by
  intro h
  exact (not_le_of_gt hcross) (h n hn)

end RHLean.Analysis.MertensExponent
