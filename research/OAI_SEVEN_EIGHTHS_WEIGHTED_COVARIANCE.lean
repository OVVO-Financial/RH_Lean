import «research.MERTENS_WEIGHTED_COVARIANCE_RH»

/-!
# OpenAI 7/8 zeta exclusion to the exact weighted signed Möbius covariance

This is a conditional quantitative transfer, using genuine arithmetic Möbius
coefficients and the exact diagonal / off-diagonal kernel from #968.

The upstream OpenAI Lean theorem lives in a distinct Lean 4.34.1 environment;
RH_Lean is pinned to Lean 4.24.0. Its substantive content is an EXPLICIT
hypothesis here, not an assumed axiom or an imported theorem. The ordinary
Littlewood zero-strip-to-power-growth direction is already kernel formalized
by MertensExponent.growthAtMost_of_strip on main.

Result: for EVERY fixed ε > 3/8 the weighted signed covariance partial sums
are uniformly bounded above. No result for ε <= 3/8, no near-minus-one
limit, and no new zero-free theorem are asserted.
-/

noncomputable section

namespace RHLean.Analysis.OAISevenEighthsCovariance

open scoped ArithmeticFunction.Moebius BigOperators
open RHLean.Analysis.WeightedMertens

/-- Input matching the asserted OAI nonvanishing in the open critical strip.
The pole/totalization at s=1 is deliberately excluded from this formulation. -/
def SevenEighthsZeroFree : Prop :=
  ∀ ρ : ℂ, MertensExponent.NontrivialZetaZero ρ →
    ρ.re ≤ (7 : ℝ) / 8

/-- Completed-zeta reflection automatically excludes the other outer wing. -/
theorem symmetric_strip_of_sevenEighths (hZF : SevenEighthsZeroFree) :
    MertensExponent.ZerosInSymmetricStrip ((7 : ℝ) / 8) := by
  intro ρ hρ
  have hr := hZF ρ hρ
  have hl := hZF (1 - ρ) (MertensExponent.nontrivialZero_one_sub hρ)
  simp only [Complex.sub_re, Complex.one_re] at hl
  constructor <;> linarith

/-- A genuine zero-free input yields all positive epsilon-loss global Mertens
power bounds. The reverse analytic direction already exists on main. -/
theorem growthAtMost_sevenEighths_of_zeroFree (hZF : SevenEighthsZeroFree) :
    MertensExponent.MertensGrowthAtMost ((7 : ℝ) / 8) :=
  MertensExponent.growthAtMost_of_strip
    (by norm_num) (symmetric_strip_of_sevenEighths hZF)

/-- Shifted reciprocal p-series used to dominate the Mertens energy at
a > 0. It is ordinary finite summation, not a statistical expectation. -/
def powerMajorant (a ε : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε - 2 * a))⁻¹

theorem powerMajorant_nonneg (a ε : ℝ) (n : ℕ) :
    0 ≤ powerMajorant a ε n := by
  unfold powerMajorant
  exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)

/-- The only analytic comparison required here is the classical p-series.
The inequality a < 1/2+ε means the majorant power is strictly >1. -/
theorem powerMajorant_summable {a ε : ℝ}
    (haε : a < (1 : ℝ) / 2 + ε) :
    Summable (powerMajorant a ε) := by
  have hp : (1 : ℝ) < 2 + 2 * ε - 2 * a := by linarith
  have hs : Summable
      (fun n : ℕ => (Real.rpow (n : ℝ) (2 + 2 * ε - 2 * a))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp
  simpa only [powerMajorant] using
    (summable_nat_add_iff 1 (G := ℝ)).2 hs

/-- Exact reciprocal-weight algebra for the same n+1 denominator in #968. -/
theorem square_power_mul_weight_eq_majorant
    (a ε : ℝ) (n : ℕ) :
    (Real.rpow (((n + 1 : ℕ) : ℝ)) a) ^ 2 *
      WeightedMertens.weight ε n = powerMajorant a ε n := by
  have hb : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hadd :
      Real.rpow (((n + 1 : ℕ) : ℝ)) (a + a) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) a *
          Real.rpow (((n + 1 : ℕ) : ℝ)) a :=
    Real.rpow_add hb a a
  have htwo :
      (Real.rpow (((n + 1 : ℕ) : ℝ)) a) ^ 2 =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a) := by
    rw [show (2 : ℝ) * a = a + a by ring, hadd]
    ring
  have hfactor :
      Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε - 2 * a) := by
    calc
      Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
          Real.rpow (((n + 1 : ℕ) : ℝ))
            ((2 * a) + (2 + 2 * ε - 2 * a)) := by
            congr 1
            ring
      _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε - 2 * a) :=
        Real.rpow_add hb _ _
  have hA : Real.rpow (((n + 1 : ℕ) : ℝ)) (2 * a) ≠ 0 :=
    (Real.rpow_pos_of_pos hb _).ne'
  have hB : Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε - 2 * a) ≠ 0 :=
    (Real.rpow_pos_of_pos hb _).ne'
  unfold WeightedMertens.weight powerMajorant
  rw [htwo, hfactor]
  field_simp [hA, hB]

/-- A genuine global Mertens power bound supplies a termwise weighted-energy
majorant. No sign independence or separate pair assumption is used. -/
theorem energy_term_le_majorant
    {a ε K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hM : ∀ n : ℕ, 1 ≤ n →
      ‖mertensSummatory n‖ ≤ K * Real.rpow (n : ℝ) a)
    (n : ℕ) :
    ‖mertensSummatory n‖ ^ 2 * WeightedMertens.weight ε n ≤
      K ^ 2 * powerMajorant a ε n := by
  have hb : 0 ≤ Real.rpow (((n + 1 : ℕ) : ℝ)) a :=
    Real.rpow_nonneg (by positivity) _
  have hbound : ‖mertensSummatory n‖ ≤
      K * Real.rpow (((n + 1 : ℕ) : ℝ)) a := by
    by_cases hn : 1 ≤ n
    · have hnle : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.le_succ n
      exact (hM n hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hnle ha) hK)
    · have hn0 : n = 0 := by omega
      subst n
      simpa [mertensSummatory_zero] using mul_nonneg hK hb
  have hsquared :
      ‖mertensSummatory n‖ ^ 2 ≤
        (K * Real.rpow (((n + 1 : ℕ) : ℝ)) a) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK hb)).2 hbound
  calc
    ‖mertensSummatory n‖ ^ 2 * WeightedMertens.weight ε n ≤
        (K * Real.rpow (((n + 1 : ℕ) : ℝ)) a) ^ 2 *
          WeightedMertens.weight ε n :=
      mul_le_mul_of_nonneg_right hsquared (WeightedMertens.weight_nonneg ε n)
    _ = K ^ 2 *
        ((Real.rpow (((n + 1 : ℕ) : ℝ)) a) ^ 2 *
          WeightedMertens.weight ε n) := by ring
    _ = K ^ 2 * powerMajorant a ε n := by
      rw [square_power_mul_weight_eq_majorant]

/-- A POWER BOUND at a < 1/2+ε implies bounded weighted-square energy.
This is an unconditional theorem about the input power bound. -/
theorem energyUpperBounded_of_powerBound {a ε : ℝ}
    (ha : 0 ≤ a) (haε : a < (1 : ℝ) / 2 + ε)
    (hM : MertensExponent.MertensPowerBound a) :
    WeightedMertens.EnergyUpperBounded ε := by
  obtain ⟨K, hK, hbound⟩ := hM
  let Q : ℝ := K ^ 2 * ∑' n : ℕ, powerMajorant a ε n
  refine ⟨Q, ?_⟩
  intro N
  calc
    WeightedMertens.energy ε N ≤
        ∑ n ∈ Finset.range N, K ^ 2 * powerMajorant a ε n := by
      unfold WeightedMertens.energy
      apply Finset.sum_le_sum
      intro n hn
      exact energy_term_le_majorant ha hK hbound n
    _ = K ^ 2 * ∑ n ∈ Finset.range N, powerMajorant a ε n := by
      rw [Finset.mul_sum]
    _ ≤ Q := by
      exact mul_le_mul_of_nonneg_left
        ((powerMajorant_summable haε).sum_le_tsum
          (Finset.range N) (fun n hn => powerMajorant_nonneg a ε n))
        (sq_nonneg _)

/-- Exact 3/8 threshold inherited from OAI's 7/8 zero-free boundary.
Every ε>3/8 is allowed, and the bound may depend on ε. -/
theorem energyUpperBounded_of_sevenEighths_zeroFree
    (hZF : SevenEighthsZeroFree) {ε : ℝ}
    (hε : (3 : ℝ) / 8 < ε) :
    WeightedMertens.EnergyUpperBounded ε := by
  let η : ℝ := (ε - (3 : ℝ) / 8) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have ha : 0 ≤ (7 : ℝ) / 8 + η := by dsimp [η]; linarith
  have haε : (7 : ℝ) / 8 + η < (1 : ℝ) / 2 + ε := by
    dsimp [η]
    linarith
  have hpower :
      MertensExponent.MertensPowerBound ((7 : ℝ) / 8 + η) :=
    (growthAtMost_sevenEighths_of_zeroFree hZF) η hη
  exact energyUpperBounded_of_powerBound ha haε hpower

/-- **OpenAI 7/8 → uniform one-sided weighted signed Möbius covariance
bound for every ε>3/8**. This uses the exact #968 diagonal-payment iff. -/
theorem covarianceUpperBounded_of_sevenEighths_zeroFree
    (hZF : SevenEighthsZeroFree) {ε : ℝ}
    (hε : (3 : ℝ) / 8 < ε) :
    WeightedMertens.CovarianceUpperBounded ε := by
  have heps : 0 < ε := by linarith
  exact (WeightedMertens.covarianceUpperBounded_iff_energyUpperBounded ε heps).2
    (energyUpperBounded_of_sevenEighths_zeroFree hZF hε)

/-- Direct unweighted, one-sided signed pair-sum power saving at 7/8.
Unlike the root/smooth normalized two-scalar Gram, the physical Green--Kubo
pair sum is NOT a Pearson correlation in [-1,1]. -/
theorem unweighted_positiveLagPairSum_upper_of_sevenEighths
    (hZF : SevenEighthsZeroFree) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      realMertensPositiveLagPairSum (n + 1) ≤
        C * Real.rpow (n : ℝ) ((7 : ℝ) / 4 + η) := by
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨K, hK, hBound⟩ :
      MertensExponent.MertensPowerBound ((7 : ℝ) / 8 + η / 2) :=
    (growthAtMost_sevenEighths_of_zeroFree hZF) (η / 2) hη2
  refine ⟨K ^ 2 / 2, div_nonneg (sq_nonneg K) (by norm_num), ?_⟩
  intro n hn
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  have hpNonneg :
      0 ≤ K * Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2) :=
    mul_nonneg hK (Real.rpow_nonneg hn0.le _)
  have hSq :
      ‖mertensSummatory n‖ ^ 2 ≤
        (K * Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2)) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hpNonneg).2 (hBound n hn)
  have hadd :
      Real.rpow (n : ℝ)
          (((7 : ℝ) / 8 + η / 2) + ((7 : ℝ) / 8 + η / 2)) =
        Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2) *
          Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2) :=
    Real.rpow_add hn0 _ _
  have hpow :
      (Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2)) ^ 2 =
        Real.rpow (n : ℝ) ((7 : ℝ) / 4 + η) := by
    calc
      (Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2)) ^ 2 =
          Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2) *
            Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2) := by ring
      _ = Real.rpow (n : ℝ)
          (((7 : ℝ) / 8 + η / 2) + ((7 : ℝ) / 8 + η / 2)) := hadd.symm
      _ = Real.rpow (n : ℝ) ((7 : ℝ) / 4 + η) := by
        congr 1
        ring
  have hEq :
      ‖mertensSummatory n‖ ^ 2 =
        realMertensDiagonal (n + 1) +
          2 * realMertensPositiveLagPairSum (n + 1) := by
    rw [norm_mertensSummatory_sq_eq_realMertensLength_sq,
      realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum]
  have hEnergy :
      realMertensDiagonal (n + 1) +
          2 * realMertensPositiveLagPairSum (n + 1) ≤
        K ^ 2 * Real.rpow (n : ℝ) ((7 : ℝ) / 4 + η) := by
    rw [← hEq]
    calc
      ‖mertensSummatory n‖ ^ 2 ≤
          (K * Real.rpow (n : ℝ) ((7 : ℝ) / 8 + η / 2)) ^ 2 := hSq
      _ = K ^ 2 * Real.rpow (n : ℝ) ((7 : ℝ) / 4 + η) := by
        rw [mul_pow, hpow]
  have hD := realMertensDiagonal_nonneg (n + 1)
  nlinarith

/-- A uniform covariance estimate at ANY ε<3/8 goes beyond the OAI baseline:
its own independent analytic L2-to-zero-strip bridge is still explicitly
required; the numerical exponent alone does not prove that bridge in Lean. -/
theorem betterThanSevenEighths_of_stronger_covariance
    {ε : ℝ} (hε : 0 < ε) (_hbetter : ε < (3 : ℝ) / 8)
    (hC : WeightedMertens.CovarianceUpperBounded ε)
    (analyticBridge : WeightedMertens.EnergyUpperBounded ε →
      MertensExponent.ZerosInSymmetricStrip ((1 : ℝ) / 2 + ε)) :
    MertensExponent.ZerosInSymmetricStrip ((1 : ℝ) / 2 + ε) :=
  analyticBridge
    ((WeightedMertens.covarianceUpperBounded_iff_energyUpperBounded ε hε).1 hC)

end RHLean.Analysis.OAISevenEighthsCovariance

#print axioms RHLean.Analysis.OAISevenEighthsCovariance.symmetric_strip_of_sevenEighths
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.powerMajorant_summable
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.square_power_mul_weight_eq_majorant
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.energy_term_le_majorant
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.energyUpperBounded_of_powerBound
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.energyUpperBounded_of_sevenEighths_zeroFree
#print axioms RHLean.Analysis.OAISevenEighthsCovariance.covarianceUpperBounded_of_sevenEighths_zeroFree
