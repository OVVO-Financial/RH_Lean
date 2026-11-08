import Mathlib
import RHLean.Analysis.DeterministicTGreenKuboComparison
import «research.VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE»
import «research.VF_MID_FLOOR_LI_DISCRETE_BACKLOG»
import «research.OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028»

/-!
# Actual prime phases, floor-Li count transport and physical square-block energy

All arithmetic refers to actual primes and the original integer Mobius source.
The phase/midpoint, floor-Li telescope, compensated ideal norm-shell, and
three-population Euler Gram identities are already proved elsewhere in RH_Lean.
This file adds an independent signed single-site/positive-pair expansion on
the ORIGINAL sharp shell and isolates spatial bias from prime-count excess.

Neither empirical equidistribution nor a power bound on signed pairs is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Actual prime count in a square block minus integer floor-Li demand. -/
def squarePhaseCountExcess (R : ℕ) : ℝ :=
  (vfMidIntegerBlockPrimeSupply R : ℝ) -
    (vfMidFloorLiBlockSupply R : ℝ)

/-- The phase module's actual prime block agrees with the original prime supply. -/
theorem squarePhaseBlockPrimeTotal_eq_actualSupply (R : ℕ) :
    vfMidSquareBlockPrimeTotal R =
      (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  unfold vfMidSquareBlockPrimeTotal vfMidIntegerBlockPrimeSupply
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]

/-- Exact floor-Li fan step, without a surrogate distribution. -/
theorem squarePhaseCountExcess_eq_floorLiBacklogStep (R : ℕ) :
    squarePhaseCountExcess R =
      (vfMidPrimeFloorLiBacklog (R + 1) : ℝ) -
        (vfMidPrimeFloorLiBacklog R : ℝ) := by
  have h := vfMidPrimeFloorLiBacklog_succ R
  have hdiff :
      (vfMidIntegerBlockPrimeSupply R : ℤ) -
          vfMidFloorLiBlockSupply R =
        vfMidPrimeFloorLiBacklog (R + 1) -
          vfMidPrimeFloorLiBacklog R := by
    omega
  unfold squarePhaseCountExcess
  exact_mod_cast hdiff

/-- The exact two-channel decomposition. Spatial phase uniformity only
controls the first summand, NOT the original total prime-count excess. -/
theorem squarePhase_leftHalfExcess_eq_bias_add_halfCountExcess
    (R : ℕ) :
    vfMidSquareBlockPrimeLeft R -
        (vfMidFloorLiBlockSupply R : ℝ) / 2 =
      vfMidSquareBlockMidpointBias R +
        squarePhaseCountExcess R / 2 := by
  unfold vfMidSquareBlockMidpointBias squarePhaseCountExcess
  rw [squarePhaseBlockPrimeTotal_eq_actualSupply]
  ring

/-- The original integer Mobius signs restricted to one natural square block. -/
def squarePhaseSignedPrefix (f : ℕ → ℝ) (R k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, f (R ^ 2 + j)

/-- Site diagonal, with all squareful zero sites retained. -/
def squarePhaseSignedDiagonal (f : ℕ → ℝ) (R k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, f (R ^ 2 + j) ^ 2

/-- Ordered signed site pairs (j < i): the original, uncentered signs. -/
def squarePhaseSignedPairs (f : ℕ → ℝ) (R k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k,
    f (R ^ 2 + i) * squarePhaseSignedPrefix f R i

@[simp] theorem squarePhaseSignedPrefix_zero (f : ℕ → ℝ) (R : ℕ) :
    squarePhaseSignedPrefix f R 0 = 0 := by
  simp [squarePhaseSignedPrefix]

@[simp] theorem squarePhaseSignedPrefix_succ
    (f : ℕ → ℝ) (R k : ℕ) :
    squarePhaseSignedPrefix f R (k + 1) =
      squarePhaseSignedPrefix f R k + f (R ^ 2 + k) := by
  simp [squarePhaseSignedPrefix, Finset.sum_range_succ]

@[simp] theorem squarePhaseSignedDiagonal_zero (f : ℕ → ℝ) (R : ℕ) :
    squarePhaseSignedDiagonal f R 0 = 0 := by
  simp [squarePhaseSignedDiagonal]

@[simp] theorem squarePhaseSignedDiagonal_succ
    (f : ℕ → ℝ) (R k : ℕ) :
    squarePhaseSignedDiagonal f R (k + 1) =
      squarePhaseSignedDiagonal f R k + f (R ^ 2 + k) ^ 2 := by
  simp [squarePhaseSignedDiagonal, Finset.sum_range_succ]

@[simp] theorem squarePhaseSignedPairs_zero (f : ℕ → ℝ) (R : ℕ) :
    squarePhaseSignedPairs f R 0 = 0 := by
  simp [squarePhaseSignedPairs]

@[simp] theorem squarePhaseSignedPairs_succ
    (f : ℕ → ℝ) (R k : ℕ) :
    squarePhaseSignedPairs f R (k + 1) =
      squarePhaseSignedPairs f R k +
        f (R ^ 2 + k) * squarePhaseSignedPrefix f R k := by
  simp [squarePhaseSignedPairs, Finset.sum_range_succ]

/-- One-shell signed positive-lag Green--Kubo identity, no |pairs|. -/
theorem squarePhaseSignedPrefix_sq_eq_diagonal_add_two_pairs
    (f : ℕ → ℝ) (R k : ℕ) :
    squarePhaseSignedPrefix f R k ^ 2 =
      squarePhaseSignedDiagonal f R k +
        2 * squarePhaseSignedPairs f R k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [squarePhaseSignedPrefix_succ, squarePhaseSignedDiagonal_succ,
        squarePhaseSignedPairs_succ]
      nlinarith only [ih]

/-- This is the ALREADY formalized original sharp physical shell, not a proxy. -/
theorem squarePhaseSignedPrefix_eq_originalSharpShell (R : ℕ) :
    squarePhaseSignedPrefix realMoebiusStep R (2 * R + 1) =
      vf919SquareShellSum R := by
  rw [vf919SquareShellSum_eq_physicalIco]
  unfold squarePhaseSignedPrefix
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : (R + 1) ^ 2 - R ^ 2 = 2 * R + 1 := by
    have hsq : (R + 1) ^ 2 = R ^ 2 + (2 * R + 1) := by ring
    omega
  rw [hlen]

/-- Actual dyadic squarefree diagonal. -/
def squarePhaseActualDyadicDiagonal (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    squarePhaseSignedDiagonal realMoebiusStep R (2 * R + 1)

/-- Complete physical signed within-shell pair term. -/
def squarePhaseActualDyadicPairs (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    squarePhaseSignedPairs realMoebiusStep R (2 * R + 1)

/-- A *new exact organization* of the existing original sharp Hecke/Euler
source: it is the actual squarefree diagonal plus twice the actual ordered
signed Möbius offdiagonal, without dropping zero modes or smooth carriers. -/
theorem oaiPaired_actualSharpEnergy_eq_squarePhaseDiagonal_add_pairs
    (H : ℕ) (hH : 4 ≤ H) :
    oaiPairedActualSharpEnergy H =
      squarePhaseActualDyadicDiagonal H +
        2 * squarePhaseActualDyadicPairs H := by
  rw [oaiPaired_actualSharpEnergy_eq_primeSampler H hH]
  unfold eulerThreeSampledShellEnergy squarePhaseActualDyadicDiagonal
    squarePhaseActualDyadicPairs
  calc
    (∑ R ∈ Finset.Ico H (2 * H), eulerThreeShellMobius R ^ 2) =
        ∑ R ∈ Finset.Ico H (2 * H),
          squarePhaseSignedPrefix realMoebiusStep R (2 * R + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro R hR
      have hR1 : 1 ≤ R := by
        have hlo := (Finset.mem_Ico.mp hR).1
        omega
      rw [← oaiPaired_realShell_eq_eulerShell R hR1,
        ← squarePhaseSignedPrefix_eq_originalSharpShell R]
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          (squarePhaseSignedDiagonal realMoebiusStep R (2 * R + 1) +
            2 * squarePhaseSignedPairs realMoebiusStep R (2 * R + 1)) := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact squarePhaseSignedPrefix_sq_eq_diagonal_add_two_pairs
        realMoebiusStep R (2 * R + 1)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Physical diagonal is bounded by site count (Mu(n)^2 <= 1). -/
theorem squarePhaseActualDyadicDiagonal_le_siteCount (H : ℕ) :
    squarePhaseActualDyadicDiagonal H ≤
      ∑ R ∈ Finset.Ico H (2 * H), ((2 * R + 1 : ℕ) : ℝ) := by
  unfold squarePhaseActualDyadicDiagonal squarePhaseSignedDiagonal
  apply Finset.sum_le_sum
  intro R _hR
  calc
    (∑ j ∈ Finset.range (2 * R + 1),
        realMoebiusStep (R ^ 2 + j) ^ 2) ≤
        ∑ _j ∈ Finset.range (2 * R + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact realMoebiusStep_sq_le_one (R ^ 2 + j)
    _ = ((2 * R + 1 : ℕ) : ℝ) := by simp

/-- Exact physical count: all H blocks together span [H^2, 4H^2). -/
theorem squarePhaseDyadicSiteCount_eq_three_sq (H : ℕ) :
    (∑ R ∈ Finset.Ico H (2 * H), ((2 * R + 1 : ℕ) : ℝ)) =
      3 * (H : ℝ) ^ 2 := by
  let g : ℕ → ℝ := fun R => (R : ℝ) ^ 2
  have hstep : ∀ R : ℕ,
      ((2 * R + 1 : ℕ) : ℝ) = g (R + 1) - g R := by
    intro R
    dsimp [g]
    push_cast
    ring
  have hle : H ≤ 2 * H := by omega
  calc
    (∑ R ∈ Finset.Ico H (2 * H), ((2 * R + 1 : ℕ) : ℝ)) =
        ∑ R ∈ Finset.Ico H (2 * H), (g (R + 1) - g R) := by
      apply Finset.sum_congr rfl
      intro R _hR
      exact hstep R
    _ = g (2 * H) - g H := by
      rw [Finset.sum_Ico_eq_sub _ hle,
        Finset.sum_range_sub, Finset.sum_range_sub]
      ring
    _ = 3 * (H : ℝ) ^ 2 := by
      dsimp [g]
      push_cast
      ring

theorem squarePhaseActualDyadicDiagonal_le_three_sq (H : ℕ) :
    squarePhaseActualDyadicDiagonal H ≤ 3 * (H : ℝ) ^ 2 := by
  exact (squarePhaseActualDyadicDiagonal_le_siteCount H).trans
    (squarePhaseDyadicSiteCount_eq_three_sq H).le

/-- NEW conditional one-sided quantitative target on exact signed pairs.
Unlike a local phase KS estimate, it would yield the native H^2 energy. -/
theorem oaiPaired_actualSharpEnergy_le_of_squarePhasePairs
    (H : ℕ) (hH : 4 ≤ H) (C : ℝ)
    (hPairs : squarePhaseActualDyadicPairs H ≤ C * (H : ℝ) ^ 2) :
    oaiPairedActualSharpEnergy H ≤ (3 + 2 * C) * (H : ℝ) ^ 2 := by
  rw [oaiPaired_actualSharpEnergy_eq_squarePhaseDiagonal_add_pairs H hH]
  have hdiag := squarePhaseActualDyadicDiagonal_le_three_sq H
  nlinarith only [hPairs, hdiag]

/-- Abstract falsifier: even EXACT zero spatial phase bias leaves the
total count discrepancy unbounded. This does not simulate actual primes. -/
theorem no_count_bound_from_halfPhaseUniformity (K : ℝ) :
    ∃ P L F : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
      L - P / 2 = 0 ∧ P - F > K := by
  refine ⟨2 * (|K| + 1), |K| + 1, 0, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · ring
  · have hK := le_abs_self K
    linarith

end RHLean.Analysis
