import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIAGONAL_BOUND»
import «research.CORRELATION_FOUR_TERMINAL_BRIDGE»

/-!
# Global returned-core synthesis

All previously separated AMP bookkeeping is now on one common weighted Mobius
clock.  Its exact square is the elementary diagonal plus twice the signed sum of
unique first-separation-owner Gram cells.  The diagonal is already root-scale,
so this file wires the sole remaining signed first-owner covariance estimate
through the existing AMP, q²-tail, CORR-4, terminal-recurrence, and RH consumers.

Consequently there is exactly one quantitative input left in this coordinate:
a root-scale upper bound for the aggregate signed first-owner covariance.  No
other packet norm, memory term, terminal term, or ownerwise estimate remains.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The sole remaining quantitative statement on the exact one-amplitude Gram.
Only the aggregate signed first-owner covariance is bounded; individual owners
are never normed. -/
def LowOwnerFirstOwnerGramBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    2 * (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerZeroFrequencyFirstOwnerGram R p) ≤
      C * (R : ℝ) ^ 2 * K

private theorem one_le_lowerEnvelope_returnedCore
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  have hm0 : mertensSummatoryInt 0 = 0 := by
    simp [mertensSummatoryInt]
  rw [hm0] at h0
  norm_num at h0
  exact h0

/-- The signed first-owner bound closes the full AMP remainder immediately,
because the exact diagonal costs at most `3 R²`. -/
theorem physicalAmplitudeRemainderBound_of_firstOwnerGramBound
    {C : ℝ} (_hC : 0 ≤ C)
    (hGram : LowOwnerFirstOwnerGramBound C) :
    LowOwnerPhysicalAmplitudeRemainderBound (C + 3) := by
  intro R K hR hK
  have hsq :=
    norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
      R hR
  have hdiag := lowOwnerZeroFrequencyMobiusDiagonal_le_three_root_sq R
  have hcross := hGram R K hR hK
  have hK1 := one_le_lowerEnvelope_returnedCore (R := R) (K := K) (by omega) hK
  have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hdiagK : 3 * (R : ℝ) ^ 2 ≤ 3 * (R : ℝ) ^ 2 * K := by
    nlinarith
  rw [hsq]
  nlinarith

/-- **Name-lock in the reverse direction.**  A root-scale bound on the full AMP
remainder already bounds the aggregate first-owner Gram with the same constant,
because the omitted diagonal in the exact square identity is nonnegative.
Thus the first-owner Gram target is not a weaker bookkeeping discrepancy: up to
the elementary diagonal in the forward direction, it is the same quantitative
AMP seam. -/
theorem firstOwnerGramBound_of_physicalAmplitudeRemainderBound
    {C : ℝ} (hAmp : LowOwnerPhysicalAmplitudeRemainderBound C) :
    LowOwnerFirstOwnerGramBound C := by
  intro R K hR hK
  have hsq :=
    norm_sq_lowOwnerPhysicalAmplitudeRemainder_zero_eq_diagonal_add_firstOwners
      R hR
  have hbound := hAmp R K hR hK
  have hdiag0 : 0 ≤ lowOwnerZeroFrequencyMobiusDiagonal R := by
    unfold lowOwnerZeroFrequencyMobiusDiagonal signedBlockEnergy
    apply Finset.sum_nonneg
    intro n _hn
    exact sq_nonneg _
  rw [hsq] at hbound
  linarith

/-- The same sole first-owner estimate therefore gives the already-compiled
LOW q² correlation inequality with coefficient `1/2`. -/
theorem correlationLowQ2Energy_of_firstOwnerGramBound
    {C : ℝ} (hC : 0 ≤ C)
    (hGram : LowOwnerFirstOwnerGramBound C) :
    CanonicalRoughCorrelationLowQ2EnergyStatementWith
      (1 / 2) (2 * (C + 3)) :=
  correlationLowQ2Energy_of_physicalAmplitudeRemainderBound
    (physicalAmplitudeRemainderBound_of_firstOwnerGramBound hC hGram)

/-- The nonrecursive q² owner tail was already absorbed in #706, so the same
bound holds on the full odd-prime daughter energy. -/
theorem correlationFullQ2Energy_of_firstOwnerGramBound
    {C : ℝ} (hC : 0 ≤ C)
    (hGram : LowOwnerFirstOwnerGramBound C) :
    CanonicalRoughCorrelationQ2EnergyStatementWith
      (1 / 2) (2 * (C + 3)) := by
  exact correlationLowQ2Energy_implies_full (by norm_num)
    (correlationLowQ2Energy_of_firstOwnerGramBound hC hGram)

private theorem farFourOddQ2DaughterEnergy_nonneg_returnedCore (R : ℕ) :
    0 ≤ farFourOddQ2DaughterEnergy R := by
  unfold farFourOddQ2DaughterEnergy
  apply Finset.sum_nonneg
  intro q _hq
  unfold rawQ2ChildEnergyReal
  positivity

/-- Coefficient `1/2` is far stronger than the already-sufficient CORR-4
interface.  Enlarging a nonnegative daughter coefficient is harmless. -/
theorem correlationFour_of_firstOwnerGramBound
    {C : ℝ} (hC : 0 ≤ C)
    (hGram : LowOwnerFirstOwnerGramBound C) :
    CanonicalRoughCorrelationFourQ2EnergyStatement := by
  let C0 : ℝ := 2 * (C + 3)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro R K hR hK
  have hhalf :=
    correlationFullQ2Energy_of_firstOwnerGramBound hC hGram R K hR hK
  have hQ := farFourOddQ2DaughterEnergy_nonneg_returnedCore R
  dsimp [C0]
  nlinarith

/-- **Single-seam RH closure.**  Once the aggregate signed first-owner Gram is
root-scale, every remaining implication is already compiled and RH follows. -/
theorem riemannHypothesis_of_firstOwnerGramBound
    {C : ℝ} (hC : 0 ≤ C)
    (hGram : LowOwnerFirstOwnerGramBound C) :
    RiemannHypothesis :=
  riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy
    (correlationFour_of_firstOwnerGramBound hC hGram)

end RHLean.Proof
