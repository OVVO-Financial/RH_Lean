import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNATURE_PAIR_ENERGY»
import «research.GLOBAL_RETURNED_CORE_DIAGONAL_BOUND»

/-!
# Audit of the proposed Boolean-cardinality collapse

The prime-signature filtration is exact, but its orientation and currency matter.

For consecutive primes `p < r` the compiled identity is

`E_p = E_r + 2 G_p`,

so the first-owner Gram is the *drop from the coarser p-level to the finer
r-level*.  Nonnegativity of the refined energy therefore gives
`2 G_p <= E_p`, not `2 G_p <= E_r`.

Moreover `E_p` is a sum of squares of whole signature-cell amplitudes, not a
sum of pointwise site squares.  The underlying AMP site is itself scalar
weighted by the reciprocal q^2 daughter coordinate and is not generally
Boolean.  The explicit R=56, n=1 computation below records this directly.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Correct orientation of one consecutive-prime energy decrement. -/
theorem two_mul_firstOwnerCellGramSum_eq_signatureEnergy_sub_successor
    {R p r : ℕ} (hpr : ConsecutivePrimeCoordinates p r) :
    2 * (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCellGram R p sig) =
      lowOwnerFirstOwnerSignatureEnergy R p -
        lowOwnerFirstOwnerSignatureEnergy R r := by
  have h :=
    lowOwnerFirstOwnerSignatureEnergy_eq_successor_add_two_gram
      (R := R) hpr
  linarith

/-- Signature energy is nonnegative because it is a sum of cell-amplitude
squares. -/
theorem lowOwnerFirstOwnerSignatureEnergy_nonneg (R p : ℕ) :
    0 ≤ lowOwnerFirstOwnerSignatureEnergy R p := by
  unfold lowOwnerFirstOwnerSignatureEnergy
  exact Finset.sum_nonneg fun sig _ => sq_nonneg _

/-- The only immediate upper bound supplied by the telescope is by the
*coarser/current* energy.  Replacing this by the refined/final energy reverses
the valid implication. -/
theorem two_mul_firstOwnerCellGramSum_le_currentSignatureEnergy
    {R p r : ℕ} (hpr : ConsecutivePrimeCoordinates p r) :
    2 * (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCellGram R p sig) ≤
      lowOwnerFirstOwnerSignatureEnergy R p := by
  rw [two_mul_firstOwnerCellGramSum_eq_signatureEnergy_sub_successor hpr]
  have hr0 := lowOwnerFirstOwnerSignatureEnergy_nonneg R r
  linarith

/-- At R=56 the genuinely recursive q^2 owners are exactly 3,5,7. -/
theorem canonicalRoughLowQ2Owners_56 :
    canonicalRoughLowQ2Owners 56 = {3, 5, 7} := by
  native_decide

/-- Concrete non-Boolean AMP coefficient: the site n=1 sees all three low-q^2
daughter windows, hence weight 1/3 + 1/5 + 1/7 = 71/105. -/
theorem lowOwnerReciprocalDaughterWeight_56_one :
    lowOwnerReciprocalDaughterWeight 56 1 = (71 : ℝ) / 105 := by
  rw [canonicalRoughLowQ2Owners_56]
  norm_num [lowOwnerReciprocalDaughterWeight, rawQ2ChildCutoff,
    squareRootEndpoint]

/-- Since mu(1)=1 and the far-tail indicator is zero at n=1<R, the actual
zero-frequency AMP site is 71/105, not a member of {-1,0,1}. -/
theorem lowOwnerZeroFrequencyMobiusSite_56_one :
    lowOwnerZeroFrequencyMobiusSite 56 1 = (71 : ℝ) / 105 := by
  rw [show lowOwnerZeroFrequencyMobiusWeight 56 1 = (71 : ℝ) / 105 by
    unfold lowOwnerZeroFrequencyMobiusWeight
    rw [lowOwnerReciprocalDaughterWeight_56_one]
    norm_num [lowOwnerFarTailWeight]]
  simp [lowOwnerZeroFrequencyMobiusSite, realMoebiusStep]

theorem lowOwnerZeroFrequencyMobiusSite_56_one_not_boolean :
    lowOwnerZeroFrequencyMobiusSite 56 1 ≠ -1 ∧
      lowOwnerZeroFrequencyMobiusSite 56 1 ≠ 0 ∧
      lowOwnerZeroFrequencyMobiusSite 56 1 ≠ 1 := by
  rw [lowOwnerZeroFrequencyMobiusSite_56_one]
  norm_num


/-- The lower-prime signature cell does not freeze the higher-q daughter
thresholds.  At R=56 and p=3, both 1 and 65 lie in the empty lower-signature
cell, but 65 has crossed the q=7 daughter cutoff 63 while 1 has not. -/
theorem signatureCell_56_three_straddles_high_q7_threshold :
    1 ∈ lowOwnerFirstOwnerSignatureCellCarrier 56 3 (∅ : Finset ℕ) ∧
      65 ∈ lowOwnerFirstOwnerSignatureCellCarrier 56 3 (∅ : Finset ℕ) ∧
      lowOwnerReciprocalDaughterWeight 56 1 -
          lowOwnerReciprocalDaughterWeight 56 65 = (1 : ℝ) / 7 := by
  have hcell :
      1 ∈ lowOwnerFirstOwnerSignatureCellCarrier 56 3 (∅ : Finset ℕ) ∧
        65 ∈ lowOwnerFirstOwnerSignatureCellCarrier 56 3 (∅ : Finset ℕ) := by
    native_decide
  refine ⟨hcell.1, hcell.2, ?_⟩
  rw [lowOwnerReciprocalDaughterWeight_56_one]
  have h65 :
      lowOwnerReciprocalDaughterWeight 56 65 = (8 : ℝ) / 15 := by
    rw [canonicalRoughLowQ2Owners_56]
    norm_num [lowOwnerReciprocalDaughterWeight, rawQ2ChildCutoff,
      squareRootEndpoint]
  rw [h65]
  norm_num

/-- The owner edge 1 -> 3 gives a second obstruction to a raw coefficient
Poincare bound: the scalar AMP weights agree, while the Mobius sign flips.
Thus the coefficient gradient is zero although the signed Gram atom is nonzero.
The full fresh-prime four-corner cancellation is needed before gradients can
control covariance. -/
theorem firstOwner_three_edge_zero_weightGradient_nonzero_siteProduct :
    IsSquarefreePairFreshPrimeOwner 3 1 3 ∧
      lowOwnerZeroFrequencyMobiusWeight 56 1 =
        lowOwnerZeroFrequencyMobiusWeight 56 3 ∧
      lowOwnerZeroFrequencyMobiusSite 56 1 *
          lowOwnerZeroFrequencyMobiusSite 56 3 ≠ 0 := by
  have howner : IsSquarefreePairFreshPrimeOwner 3 1 3 := by
    native_decide
  have hthree :
      lowOwnerReciprocalDaughterWeight 56 3 = (71 : ℝ) / 105 := by
    rw [canonicalRoughLowQ2Owners_56]
    norm_num [lowOwnerReciprocalDaughterWeight, rawQ2ChildCutoff,
      squareRootEndpoint]
  have hweight1 :
      lowOwnerZeroFrequencyMobiusWeight 56 1 = (71 : ℝ) / 105 := by
    unfold lowOwnerZeroFrequencyMobiusWeight
    rw [lowOwnerReciprocalDaughterWeight_56_one]
    norm_num [lowOwnerFarTailWeight]
  have hweight3 :
      lowOwnerZeroFrequencyMobiusWeight 56 3 = (71 : ℝ) / 105 := by
    unfold lowOwnerZeroFrequencyMobiusWeight
    rw [hthree]
    norm_num [lowOwnerFarTailWeight]
  have hsite3 :
      lowOwnerZeroFrequencyMobiusSite 56 3 = -((71 : ℝ) / 105) := by
    unfold lowOwnerZeroFrequencyMobiusSite
    rw [hweight3]
    have hflip :=
      realMoebiusStep_mul_prime_eq_neg
        (p := 3) (n := 1) (by norm_num : Nat.Prime 3) (by norm_num : ¬ 3 ∣ 1)
    have hmu1 : realMoebiusStep 1 = 1 := by
      norm_num [realMoebiusStep]
    have hmu3 : realMoebiusStep 3 = -1 := by
      simpa [hmu1] using hflip
    rw [hmu3]
    ring
  refine ⟨howner, ?_, ?_⟩
  · rw [hweight1, hweight3]
  · rw [lowOwnerZeroFrequencyMobiusSite_56_one, hsite3]
    norm_num

end RHLean.Proof
