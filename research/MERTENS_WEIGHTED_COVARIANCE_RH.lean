import RHLean.Analysis.MathlibMertensHook
import «research.MERTENS_CONVERSE_IDENTIFICATION»

/-!
# Weighted signed Möbius covariance and the Mertens/RH criterion

This module uses the genuine Möbius summatory function and existing
Green--Kubo pair carrier. It formalizes the EXACT finite weighted identity
and the equivalence between bounded signed weighted pair prefixes and bounded
nonnegative weighted Mertens energies (for every positive epsilon).

The analytic implication from weighted L2 energy to zero-free half planes
is a separate Mellin/Cauchy--Schwarz step. An explicit bridge proposition
below records that obligation. It is NOT an axiom, not discharged here,
and this module does not assert RH or unconditional energy boundedness.
See the adjacent research note for the classical proof and known status.
-/

noncomputable section

namespace RHLean.Analysis.WeightedMertens

open scoped ArithmeticFunction.Moebius BigOperators

/-- Strictly positive reciprocal weight of the n-th Mertens prefix. We use
n+1 in the denominator to avoid an artificial singularity at n=0. -/
def weight (ε : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε))⁻¹

theorem weight_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ weight ε n := by
  unfold weight
  exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)

/-- Finite weighted Mertens-square energy (genuine complex Mertens norm). -/
def energy (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ‖mertensSummatory n‖ ^ 2 * weight ε n

/-- The true squarefree diagonal, with exactly the same weights. -/
def diagonal (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, realMertensDiagonal (n + 1) * weight ε n

/-- The complete ordered-pair signed covariance, with no pair omitted. -/
def covariance (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    realMertensPositiveLagPairSum (n + 1) * weight ε n

theorem energy_nonneg (ε : ℝ) (N : ℕ) : 0 ≤ energy ε N := by
  unfold energy
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (sq_nonneg _) (weight_nonneg ε n)

theorem diagonal_nonneg (ε : ℝ) (N : ℕ) : 0 ≤ diagonal ε N := by
  unfold diagonal
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (realMertensDiagonal_nonneg _) (weight_nonneg ε n)

/-- Exact finite zero-target identity: energy = diagonal + 2 covariance.
This preserves the actual Möbius coefficients and every pair m < n. -/
theorem energy_eq_diagonal_add_two_covariance (ε : ℝ) (N : ℕ) :
    energy ε N = diagonal ε N + 2 * covariance ε N := by
  unfold energy diagonal covariance
  calc
    (∑ n ∈ Finset.range N, ‖mertensSummatory n‖ ^ 2 * weight ε n) =
      ∑ n ∈ Finset.range N,
        (realMertensDiagonal (n + 1) * weight ε n +
          2 * (realMertensPositiveLagPairSum (n + 1) * weight ε n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mertensSummatory_sq_eq_realMertensLength_sq,
          realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum]
        ring
    _ = (∑ n ∈ Finset.range N, realMertensDiagonal (n + 1) * weight ε n) +
        2 * (∑ n ∈ Finset.range N,
          realMertensPositiveLagPairSum (n + 1) * weight ε n) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The covariance is literally the n-weighted sum over ordered Möbius pairs. -/
theorem covariance_eq_ordered_pairs (ε : ℝ) (N : ℕ) :
    covariance ε N =
      ∑ n ∈ Finset.range N,
        (∑ b ∈ Finset.range (n + 1),
          ∑ a ∈ Finset.range b, realMoebiusStep a * realMoebiusStep b) *
          weight ε n := by
  unfold covariance
  apply Finset.sum_congr rfl
  intro n hn
  rw [realMertensPositiveLagPairSum_eq_doubleSum]

/-- A pointwise upper bound on the diagonal is paid without any Möbius-sign
hypothesis, at its natural squarefree count. -/
theorem diagonal_le_linear_majorant (ε : ℝ) (N : ℕ) :
    diagonal ε N ≤
      ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)) * weight ε n := by
  unfold diagonal
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_right
    (realMertensDiagonal_le (n + 1)) (weight_nonneg ε n)

/-- The majorant is an ordinary shifted p-series with exponent 1+2ε. -/
def majorant (ε : ℝ) (n : ℕ) : ℝ :=
  (Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε))⁻¹

theorem majorant_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ majorant ε n := by
  unfold majorant
  exact inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)

theorem linear_weight_eq_majorant (ε : ℝ) (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)) * weight ε n = majorant ε n := by
  have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hone :
      Real.rpow (((n + 1 : ℕ) : ℝ)) (1 : ℝ) =
        (((n + 1 : ℕ) : ℝ)) :=
    Real.rpow_one _
  have hadd :
      Real.rpow (((n + 1 : ℕ) : ℝ)) ((1 : ℝ) + (1 + 2 * ε)) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (1 : ℝ) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε) :=
    Real.rpow_add hbase _ _
  have hpow :
      Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
        (((n + 1 : ℕ) : ℝ)) *
          Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε) := by
    calc
      Real.rpow (((n + 1 : ℕ) : ℝ)) (2 + 2 * ε) =
          Real.rpow (((n + 1 : ℕ) : ℝ)) ((1 : ℝ) + (1 + 2 * ε)) := by
            congr 1
            ring
      _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (1 : ℝ) *
            Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε) := hadd
      _ = (((n + 1 : ℕ) : ℝ)) *
            Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε) := by rw [hone]
  have hpos : 0 < Real.rpow (((n + 1 : ℕ) : ℝ)) (1 + 2 * ε) :=
    Real.rpow_pos_of_pos hbase _
  unfold weight majorant
  rw [hpow]
  field_simp [hbase.ne', hpos.ne']


theorem majorant_summable (ε : ℝ) (hε : 0 < ε) :
    Summable (majorant ε) := by
  have hp : (1 : ℝ) < 1 + 2 * ε := by linarith
  have hs : Summable
      (fun n : ℕ => (Real.rpow (n : ℝ) (1 + 2 * ε))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hp
  simpa only [majorant] using!
    (summable_nat_add_iff 1 (G := ℝ)).2 hs

/-- The diagonal is UNCONDITIONALLY uniformly bounded for each ε>0.
The constant is the convergent positive p-series sum. -/
theorem diagonal_uniform_bounded (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, diagonal ε N ≤ D := by
  let D : ℝ := ∑' n : ℕ, majorant ε n
  have hD : 0 ≤ D := by
    dsimp [D]
    exact tsum_nonneg (majorant_nonneg ε)
  refine ⟨D, hD, ?_⟩
  intro N
  calc
    diagonal ε N ≤
        ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)) * weight ε n :=
      diagonal_le_linear_majorant ε N
    _ = ∑ n ∈ Finset.range N, majorant ε n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact linear_weight_eq_majorant ε n
    _ ≤ D := (majorant_summable ε hε).sum_le_tsum
      (Finset.range N) (fun n _hn => majorant_nonneg ε n)

/-- The actual outstanding signed one-sided assumption for a single ε.
No absolute covariance or pairwise sign assumption is introduced. -/
def CovarianceUpperBounded (ε : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, covariance ε N ≤ C

def EnergyUpperBounded (ε : ℝ) : Prop :=
  ∃ E : ℝ, ∀ N : ℕ, energy ε N ≤ E

theorem covarianceUpperBounded_iff_energyUpperBounded
    (ε : ℝ) (hε : 0 < ε) :
    CovarianceUpperBounded ε ↔ EnergyUpperBounded ε := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨D, hD, hdiag⟩ := diagonal_uniform_bounded ε hε
    refine ⟨D + 2 * C, ?_⟩
    intro N
    rw [energy_eq_diagonal_add_two_covariance]
    have hc := hC N
    have hd := hdiag N
    linarith
  · rintro ⟨E, hE⟩
    refine ⟨E / 2, ?_⟩
    intro N
    have he := hE N
    have hd := diagonal_nonneg ε N
    rw [energy_eq_diagonal_add_two_covariance] at he
    linarith

/-- The epsilon family posed in the user's research question. -/
def AllCovarianceUpperBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → CovarianceUpperBounded ε

def AllEnergyUpperBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → EnergyUpperBounded ε

/-- Entirely arithmetic equivalence: diagonal is automatically paid and only
the one-sided signed off-diagonal upper envelope is outstanding. -/
theorem allCovariance_iff_allEnergy :
    AllCovarianceUpperBounded ↔ AllEnergyUpperBounded := by
  constructor
  · intro h ε hε
    exact (covarianceUpperBounded_iff_energyUpperBounded ε hε).mp (h ε hε)
  · intro h ε hε
    exact (covarianceUpperBounded_iff_energyUpperBounded ε hε).mpr (h ε hε)

/-- A stated analytic L2-to-zero-strip obligation.
Its classical mathematical proof is Cauchy--Schwarz, Abel/Mellin continuation,
the reciprocal zeta identity and functional-equation reflection. The same
conclusion is not inferred from positivity or an identity alone. -/
def WeightedEnergyMellinCriterion : Prop :=
  AllEnergyUpperBounded →
    MertensExponent.ZerosInSymmetricStrip ((1 : ℝ) / 2)

/-- Conditional forward consumer, with the precise analytic hypothesis visible.
This does NOT provide the missing L2-to-Mellin lemma. -/
theorem criticalZeros_of_covariance
    (analyticBridge : WeightedEnergyMellinCriterion)
    (hC : AllCovarianceUpperBounded) :
    MertensExponent.ZerosInSymmetricStrip ((1 : ℝ) / 2) :=
  analyticBridge (allCovariance_iff_allEnergy.mp hC)

end RHLean.Analysis.WeightedMertens

-- Acceptance is an audit of the ACTUAL inferred axioms, not merely a type check.
#print axioms RHLean.Analysis.WeightedMertens.energy_eq_diagonal_add_two_covariance
#print axioms RHLean.Analysis.WeightedMertens.covariance_eq_ordered_pairs
#print axioms RHLean.Analysis.WeightedMertens.diagonal_uniform_bounded
#print axioms RHLean.Analysis.WeightedMertens.covarianceUpperBounded_iff_energyUpperBounded
#print axioms RHLean.Analysis.WeightedMertens.allCovariance_iff_allEnergy
#print axioms RHLean.Analysis.WeightedMertens.criticalZeros_of_covariance
