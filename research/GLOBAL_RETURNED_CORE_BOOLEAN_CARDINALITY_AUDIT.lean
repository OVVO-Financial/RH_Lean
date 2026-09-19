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

end RHLean.Proof
