import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_OWNER_PARENT_CONTINUATION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»

/-!
# Deterministic cancellation in the inherited reciprocal ledger

On the nonzero physical squarefree carrier, the Euler normalization in the
owner-labelled inherited energy cancels the reciprocal Möbius denominator
exactly.  The remaining quantity is a deterministic mixed-incidence square of
the threshold potential.

This file does not estimate that square.  It only changes currency exactly,
retaining the first owner `p`, next owner `r`, stripped parent, and the literal
`multiplicity / r^2` weight.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The mixed second incidence of the threshold potential, before Euler
normalization. -/
def lowOwnerThresholdMixedIncidencePairEnergy
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdSecondOwnerDifference R p r parent.1 ^ 2 *
    lowOwnerThresholdSecondOwnerDifference R p r parent.2 ^ 2

/-- Multiplicative second incidences commute exactly. -/
theorem lowOwnerThresholdSecondOwnerDifference_comm
    (R p r n : ℕ) :
    lowOwnerThresholdSecondOwnerDifference R p r n =
      lowOwnerThresholdSecondOwnerDifference R r p n := by
  unfold lowOwnerThresholdSecondOwnerDifference
    lowOwnerThresholdOwnerIncidenceWeight
  have hmul : p * (r * n) = r * (p * n) := by ring
  rw [hmul]
  ring

/-- Hence the critical Euler coordinate is symmetric in the two owner labels. -/
theorem lowOwnerThresholdCriticalEulerDifference_comm
    {R p r n : ℕ} (hp : 0 < p) (hr : 0 < r) :
    lowOwnerThresholdCriticalEulerDifference R p r n =
      lowOwnerThresholdCriticalEulerDifference R r p n := by
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr,
    lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hp,
    lowOwnerThresholdSecondOwnerDifference_comm]

/-- The retained pair coefficient is therefore symmetric in the two owner
labels as well. -/
theorem lowOwnerThresholdEulerPairCoefficient_comm
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hp : 0 < p) (hr : 0 < r) :
    lowOwnerThresholdEulerPairCoefficient R p r parent =
      lowOwnerThresholdEulerPairCoefficient R r p parent := by
  unfold lowOwnerThresholdEulerPairCoefficient
  rw [lowOwnerThresholdCriticalEulerDifference_comm hp hr,
    lowOwnerThresholdCriticalEulerDifference_comm hp hr]

private theorem realMoebiusStep_sq_eq_one_of_ne_zero
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) :
    realMoebiusStep n ^ 2 = 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h] at hn ⊢

/-- On a nonzero reciprocal pair the reciprocal energy is literally
`1 / (a^2 b^2)`. -/
theorem postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_of_nonzero
    {a b : ℕ}
    (ha : realMoebiusStep a ≠ 0)
    (hb : realMoebiusStep b ≠ 0) :
    postRootCovarianceReciprocalPairEnergy (a, b) =
      1 / (((a : ℝ) ^ 2) * ((b : ℝ) ^ 2)) := by
  have hma := realMoebiusStep_sq_eq_one_of_ne_zero ha
  have hmb := realMoebiusStep_sq_eq_one_of_ne_zero hb
  unfold postRootCovarianceReciprocalPairEnergy
    postRootCovarianceReciprocalPairAmplitude
  rw [div_pow]
  rw [mul_pow, hma, hmb]
  ring

/-- **Exact Möbius/denominator cancellation.**

After replacing each critical Euler difference by `n * Δ_r Δ_p F_R(n)`, the
`a^2 b^2` Euler factors cancel the reciprocal pair energy exactly. -/
theorem lowOwnerThresholdEulerParentEnergy_eq_mixedIncidence
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hr : 0 < r)
    (haPos : 0 < parent.1) (hbPos : 0 < parent.2)
    (haMu : realMoebiusStep parent.1 ≠ 0)
    (hbMu : realMoebiusStep parent.2 ≠ 0) :
    lowOwnerThresholdEulerParentEnergy R p r parent =
      lowOwnerThresholdMixedIncidencePairEnergy R p r parent := by
  have ha0 : (parent.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt haPos)
  have hb0 : (parent.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hbPos)
  rw [lowOwnerThresholdEulerParentEnergy]
  rw [postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_of_nonzero
    haMu hbMu]
  unfold lowOwnerThresholdEulerPairCoefficient
    lowOwnerThresholdMixedIncidencePairEnergy
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr,
    lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr]
  field_simp [ha0, hb0]

/-- The literal fixed-owner inherited child sum is therefore the physical
`multiplicity / r^2` weight times the deterministic mixed-incidence energy. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq_mixedIncidence
    {R p r : ℕ} (hr : r.Prime) {parent : ℕ × ℕ}
    (haPos : 0 < parent.1) (hbPos : 0 < parent.2)
    (haMu : realMoebiusStep parent.1 ≠ 0)
    (hbMu : realMoebiusStep parent.2 ≠ 0) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child) =
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 *
        lowOwnerThresholdMixedIncidencePairEnergy R p r parent := by
  rw [sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq hr]
  rw [lowOwnerThresholdEulerParentEnergy_eq_mixedIncidence
    hr.pos haPos hbPos haMu hbMu]

private theorem prime_of_mem_squarefreePairFreshPrimeSet_inherited
    {q a b : ℕ}
    (hq : q ∈ squarefreePairFreshPrimeSet a b) :
    q.Prime := by
  simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
    Finset.mem_sdiff] at hq
  rcases hq with hq | hq
  · have hpf : q ∈ a.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    exact Nat.prime_of_mem_primeFactors hpf
  · have hpf : q ∈ b.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    exact Nat.prime_of_mem_primeFactors hpf

/-- Membership in the fresh set of the ordered stripped parent is, up to the
harmless coordinate swap used by `squarefreePairPrimeOrderedParent`, membership
in the raw stripped pair. -/
theorem mem_rawStrippedFresh_of_mem_primeOrderedParentFresh
    {r m n q : ℕ}
    (hq : q ∈ squarefreePairFreshPrimeSet
      (squarefreePairPrimeOrderedParent r m n).1
      (squarefreePairPrimeOrderedParent r m n).2) :
    q ∈ squarefreePairFreshPrimeSet
      (squarefreePrimeFamilyParent r m)
      (squarefreePrimeFamilyParent r n) := by
  unfold squarefreePairPrimeOrderedParent at hq
  dsimp only at hq
  by_cases hlt : squarefreePrimeFamilyParent r m <
      squarefreePrimeFamilyParent r n
  · simpa [hlt] using hq
  · have hswap : q ∈ squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent r n)
        (squarefreePrimeFamilyParent r m) := by
      simpa [hlt] using hq
    rw [squarefreePairFreshPrimeSet_comm]
    exact hswap

/-- **Exterior-owner bracket.**  Every fresh coordinate remaining on a
`(p,sig,r,parent)` block lies strictly between its first and greatest owners. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_fresh_between_owners
    {R p r q : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r)
    (hq : q ∈ squarefreePairFreshPrimeSet parent.1 parent.2) :
    p < q ∧ q < r := by
  rcases lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_has_positiveWitness
      hparent with ⟨m, n, hmn, hparentEq⟩
  have hqOrdered := hq
  rw [← hparentEq] at hqOrdered
  have hqr : q < r :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_fresh_lt_owner
      hp hmn hqOrdered
  have hrData := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
  have hrPrime : r.Prime := hrData.1
  have hqRaw := mem_rawStrippedFresh_of_mem_primeOrderedParentFresh hqOrdered
  have hqPrime : q.Prime :=
    prime_of_mem_squarefreePairFreshPrimeSet_inherited hqRaw
  have hqrNe : q ≠ r := Nat.ne_of_lt hqr
  have hoff := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  have hqChild : q ∈ squarefreePairFreshPrimeSet m n :=
    (mem_freshPrimeSet_stripped_iff_of_ne
      hrPrime hqPrime hqrNe hmPos hnPos).1 hqRaw
  have hpq : p < q :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner hp hmAd hnAd hqChild
  exact ⟨hpq, hqr⟩

end RHLean.Proof
