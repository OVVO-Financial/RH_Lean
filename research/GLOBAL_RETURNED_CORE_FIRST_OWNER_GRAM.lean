import Mathlib
import «research.GLOBAL_RETURNED_CORE_ONE_AMPLITUDE»

/-!
# Exact global first-separation Gram expansion of the AMP amplitude

The zero-frequency AMP remainder is already one real weighted Möbius sum.  This
file squares that one amplitude exactly and assigns every off-diagonal Gram atom
to its unique least fresh-prime owner.  The owner partition is purely
combinatorial and therefore survives the nonconstant AMP site weights without
any domination or triangle inequality.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Diagonal energy of the one AMP trajectory. -/
def lowOwnerZeroFrequencyMobiusDiagonal (R : ℕ) : ℝ :=
  signedBlockEnergy (lowOwnerZeroFrequencyMobiusSite R)
    (squareRootEndpoint R + 1)

/-- Full off-diagonal Gram covariance of the one AMP trajectory. -/
def lowOwnerZeroFrequencyMobiusGram (R : ℕ) : ℝ :=
  signedBlockCrossCovariance (lowOwnerZeroFrequencyMobiusSite R)
    (squareRootEndpoint R + 1)

@[simp] theorem lowOwnerZeroFrequencyMobiusSite_zero (R : ℕ) :
    lowOwnerZeroFrequencyMobiusSite R 0 = 0 := by
  simp [lowOwnerZeroFrequencyMobiusSite, realMoebiusStep]

/-- The Icc amplitude is literally the ordinary prefix sum because the omitted
zero Möbius site has weight zero. -/
theorem lowOwnerZeroFrequencyMobiusAmplitude_eq_signedBlockPrefix
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusAmplitude R =
      signedBlockPrefix (lowOwnerZeroFrequencyMobiusSite R)
        (squareRootEndpoint R + 1) := by
  unfold lowOwnerZeroFrequencyMobiusAmplitude signedBlockPrefix
  have hset :
      Finset.range (squareRootEndpoint R + 1) =
        insert 0 (Finset.Icc 1 (squareRootEndpoint R)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  rw [hset]
  simp

/-- **Exact global square expansion.** -/
theorem lowOwnerZeroFrequencyMobiusAmplitude_sq_eq_diagonal_add_two_gram
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusAmplitude R ^ 2 =
      lowOwnerZeroFrequencyMobiusDiagonal R +
        2 * lowOwnerZeroFrequencyMobiusGram R := by
  rw [lowOwnerZeroFrequencyMobiusAmplitude_eq_signedBlockPrefix]
  exact signedBlockPrefix_sq_eq_energy_add_two_mul_cross
    (lowOwnerZeroFrequencyMobiusSite R) (squareRootEndpoint R + 1)

/-- The Gram is literally the unordered physical pair sum on the common clock. -/
theorem lowOwnerZeroFrequencyMobiusGram_eq_physicalPairs (R : ℕ) :
    lowOwnerZeroFrequencyMobiusGram R =
      squareRunPhysicalPairCovariance (lowOwnerZeroFrequencyMobiusSite R)
        0 (squareRootEndpoint R + 1) := by
  have h := signedBlockInnerCovariance_eq_squareRunPhysicalPairCovariance
    (lowOwnerZeroFrequencyMobiusSite R)
    (A := 0) (B := squareRootEndpoint R + 1) (Nat.zero_le _)
  unfold lowOwnerZeroFrequencyMobiusGram signedBlockInnerCovariance at h ⊢
  simp at h
  exact h

/-- Owner-projector expansion of one weighted AMP pair. -/
def lowOwnerZeroFrequencyFreshPrimeOwnerExpansion
    (R X m n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo X,
    if IsSquarefreePairFreshPrimeOwner p m n then
      lowOwnerZeroFrequencyMobiusSite R m *
        lowOwnerZeroFrequencyMobiusSite R n
    else 0

/-- Unique-owner reconstruction is unchanged by the scalar AMP site weights. -/
theorem lowOwnerZeroFrequencyFreshPrimeOwnerExpansion_eq_pairWeight
    {R X m n : ℕ} (hmn : m < n) (hnX : n ≤ X) :
    lowOwnerZeroFrequencyFreshPrimeOwnerExpansion R X m n =
      lowOwnerZeroFrequencyMobiusSite R m *
        lowOwnerZeroFrequencyMobiusSite R n := by
  unfold lowOwnerZeroFrequencyFreshPrimeOwnerExpansion
    lowOwnerZeroFrequencyMobiusSite
  have hbase := squarefreePairFreshPrimeOwnerExpansion_eq_pairWeight hmn hnX
  unfold squarefreePairFreshPrimeOwnerExpansion at hbase
  calc
    (∑ p ∈ primesUpTo X,
        if IsSquarefreePairFreshPrimeOwner p m n then
          (lowOwnerZeroFrequencyMobiusWeight R m * realMoebiusStep m) *
            (lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n)
        else 0) =
      (lowOwnerZeroFrequencyMobiusWeight R m *
        lowOwnerZeroFrequencyMobiusWeight R n) *
        (∑ p ∈ primesUpTo X,
          if IsSquarefreePairFreshPrimeOwner p m n then
            realMoebiusStep m * realMoebiusStep n
          else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        split <;> ring
    _ = (lowOwnerZeroFrequencyMobiusWeight R m *
          lowOwnerZeroFrequencyMobiusWeight R n) *
        (realMoebiusStep m * realMoebiusStep n) := by rw [hbase]
    _ = (lowOwnerZeroFrequencyMobiusWeight R m * realMoebiusStep m) *
          (lowOwnerZeroFrequencyMobiusWeight R n * realMoebiusStep n) := by ring

/-- Weighted covariance carried by one least fresh-prime owner. -/
def lowOwnerZeroFrequencyFirstOwnerGram (R p : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 0 (squareRootEndpoint R + 1),
    ∑ m ∈ Finset.Ico 0 n,
      if IsSquarefreePairFreshPrimeOwner p m n then
        lowOwnerZeroFrequencyMobiusSite R m *
          lowOwnerZeroFrequencyMobiusSite R n
      else 0

/-- **Global first-separation Fubini for the actual AMP Gram.**  Every
weighted off-diagonal pair is assigned once and only once to its chronological
fresh-prime owner. -/
theorem lowOwnerZeroFrequencyMobiusGram_eq_sum_firstOwnerGram
    (R : ℕ) :
    lowOwnerZeroFrequencyMobiusGram R =
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerZeroFrequencyFirstOwnerGram R p := by
  rw [lowOwnerZeroFrequencyMobiusGram_eq_physicalPairs]
  unfold squareRunPhysicalPairCovariance lowOwnerZeroFrequencyFirstOwnerGram
  calc
    (∑ n ∈ Finset.Ico 0 (squareRootEndpoint R + 1),
        ∑ m ∈ Finset.Ico 0 n,
          lowOwnerZeroFrequencyMobiusSite R m *
            lowOwnerZeroFrequencyMobiusSite R n) =
      ∑ n ∈ Finset.Ico 0 (squareRootEndpoint R + 1),
        ∑ m ∈ Finset.Ico 0 n,
          lowOwnerZeroFrequencyFreshPrimeOwnerExpansion
            R (squareRootEndpoint R) m n := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m < n := (Finset.mem_Ico.mp hm).2
      have hnX : n ≤ squareRootEndpoint R := by
        have hnlt := (Finset.mem_Ico.mp hn).2
        omega
      rw [lowOwnerZeroFrequencyFreshPrimeOwnerExpansion_eq_pairWeight hmn hnX]
    _ = ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ n ∈ Finset.Ico 0 (squareRootEndpoint R + 1),
          ∑ m ∈ Finset.Ico 0 n,
            if IsSquarefreePairFreshPrimeOwner p m n then
              lowOwnerZeroFrequencyMobiusSite R m *
                lowOwnerZeroFrequencyMobiusSite R n
            else 0 := by
      unfold lowOwnerZeroFrequencyFreshPrimeOwnerExpansion
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = _ := rfl

/-- The actual AMP remainder energy is therefore diagonal plus twice the unique
first-owner Gram, with no packetwise norm loss. -/
theorem norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
    (R : ℕ) (hR : 56 ≤ R) :
    ‖lowOwnerPhysicalAmplitudeRemainder R 0‖ ^ 2 =
      lowOwnerZeroFrequencyMobiusDiagonal R +
        2 * ∑ p ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerZeroFrequencyFirstOwnerGram R p := by
  rw [norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_oneAmplitude_sq R hR,
    lowOwnerZeroFrequencyMobiusAmplitude_sq_eq_diagonal_add_two_gram,
    lowOwnerZeroFrequencyMobiusGram_eq_sum_firstOwnerGram]

end RHLean.Proof
