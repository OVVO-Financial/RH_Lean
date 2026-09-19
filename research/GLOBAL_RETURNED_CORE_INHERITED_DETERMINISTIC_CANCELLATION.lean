import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_OWNER_PARENT_CONTINUATION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»

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

/-- One threshold atom in the mixed `(p,r)` incidence, written on the `p`
window.  For `p < r`, the two windows are disjoint. -/
def lowOwnerThresholdAtomicMixedDifference
    (p r n y : ℕ) : ℝ :=
  lowOwnerThresholdCrossingIndicator p n y -
    lowOwnerThresholdCrossingIndicator p (r * n) y

/-- **Exact atomic square identity.**  When `p < r` and the site is positive,
the two multiplicative threshold windows cannot be simultaneously active, so
squaring loses nothing: the square of their signed difference is exactly their
activity count. -/
theorem lowOwnerThresholdAtomicMixedDifference_sq_eq_activity
    {p r n y : ℕ} (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdAtomicMixedDifference p r n y ^ 2 =
      lowOwnerThresholdCrossingIndicator p n y +
        lowOwnerThresholdCrossingIndicator p (r * n) y := by
  have hpnrn : p * n < r * n :=
    Nat.mul_lt_mul_of_pos_right hpr hn
  unfold lowOwnerThresholdAtomicMixedDifference
    lowOwnerThresholdCrossingIndicator
  by_cases hleft : n ≤ y ∧ y < p * n
  · by_cases hright : r * n ≤ y ∧ y < p * (r * n)
    · exfalso
      omega
    · simp [hleft, hright]
  · by_cases hright : r * n ≤ y ∧ y < p * (r * n)
    · simp [hleft, hright]
    · simp [hleft, hright]

/-- The existing clipped-edge coordinate is exactly the atomic mixed window. -/
theorem lowOwnerThresholdClippedDifference_eq_atomicMixedDifference
    {p r n y : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) :
    lowOwnerThresholdClippedDifference p r n y =
      lowOwnerThresholdAtomicMixedDifference p r n y := by
  unfold lowOwnerThresholdClippedDifference
    lowOwnerThresholdAtomicMixedDifference
  exact (lowOwnerThresholdCrossing_secondIncidence_comm hp hr).symm

private theorem lowOwnerInheritedReciprocalSquareBudget_le_quarter (R : ℕ) :
    (∑ q ∈ canonicalRoughLowQ2Owners R, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤
      1 / 4 := by
  have hsub : canonicalRoughLowQ2Owners R ⊆ (primesUpTo (R - 1)).erase 2 :=
    Finset.sdiff_subset
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤
        ∑ q ∈ (primesUpTo (R - 1)).erase 2, ((1 : ℝ) / (q : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q _hq _hnot
      positivity
    _ ≤ 1 / 4 := by
      simpa [div_pow] using
        (oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter (R - 1))

/-- **Quarter-budget daughter square.**  Cauchy--Schwarz costs exactly the
compiled odd-prime reciprocal-square budget, while #744 turns each atomic
square into the sum of two disjoint crossing indicators. -/
theorem lowOwnerThresholdDaughterClippedSum_sq_le_quarter_activity
    {R p r n : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) (hn : 0 < n) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) *
        lowOwnerThresholdClippedDifference
          p r n (rawQ2ChildCutoff R q)) ^ 2 ≤
      (1 / 4 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
  let S := canonicalRoughLowQ2Owners R
  let b : ℕ → ℝ := fun q =>
    lowOwnerThresholdClippedDifference p r n (rawQ2ChildCutoff R q)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (R := ℝ) S (fun q => (1 : ℝ) / (q : ℝ)) b
  have hbSq :
      (∑ q ∈ S, b q ^ 2) =
        ∑ q ∈ S,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
    apply Finset.sum_congr rfl
    intro q _hq
    unfold b
    rw [lowOwnerThresholdClippedDifference_eq_atomicMixedDifference
      hp.one_le hr.one_le]
    exact lowOwnerThresholdAtomicMixedDifference_sq_eq_activity hpr hn
  have hbudget :
      (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4 := by
    exact lowOwnerInheritedReciprocalSquareBudget_le_quarter R
  have hbNonneg : 0 ≤ ∑ q ∈ S, b q ^ 2 := by
    apply Finset.sum_nonneg
    intro q _hq
    positivity
  calc
    (∑ q ∈ canonicalRoughLowQ2Owners R,
        ((1 : ℝ) / (q : ℝ)) *
          lowOwnerThresholdClippedDifference
            p r n (rawQ2ChildCutoff R q)) ^ 2 =
        (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) * b q) ^ 2 := by rfl
    _ ≤ (∑ q ∈ S, ((1 : ℝ) / (q : ℝ)) ^ 2) *
          ∑ q ∈ S, b q ^ 2 := hcs
    _ ≤ (1 / 4 : ℝ) * ∑ q ∈ S, b q ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget hbNonneg
    _ = (1 / 4 : ℝ) *
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q)) := by
      rw [hbSq]

/-- **Pointwise mixed-incidence square bound.**  The full threshold second
difference costs one half of the daughter activity plus twice the two root
crossing indicators.  No logarithmic factor and no Möbius estimate enters. -/
theorem lowOwnerThresholdSecondOwnerDifference_sq_le_activity
    {R p r n : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 ≤
      (1 / 2 : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) +
      2 *
        (lowOwnerThresholdCrossingIndicator p n (R - 1) +
          lowOwnerThresholdCrossingIndicator p (r * n) (R - 1)) := by
  let A : ℝ :=
    ∑ q ∈ canonicalRoughLowQ2Owners R,
      ((1 : ℝ) / (q : ℝ)) *
        lowOwnerThresholdClippedDifference
          p r n (rawQ2ChildCutoff R q)
  let B : ℝ := lowOwnerThresholdClippedDifference p r n (R - 1)
  have hrewrite :
      lowOwnerThresholdSecondOwnerDifference R p r n = A - B := by
    simpa [A, B] using
      (lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
        hR hp.one_le hr.one_le)
  have hA : A ^ 2 ≤
      (1 / 4 : ℝ) *
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) := by
    simpa [A] using
      (lowOwnerThresholdDaughterClippedSum_sq_le_quarter_activity
        (R := R) hp hr hpr hn)
  have hB : B ^ 2 =
      lowOwnerThresholdCrossingIndicator p n (R - 1) +
        lowOwnerThresholdCrossingIndicator p (r * n) (R - 1) := by
    unfold B
    rw [lowOwnerThresholdClippedDifference_eq_atomicMixedDifference
      hp.one_le hr.one_le]
    exact lowOwnerThresholdAtomicMixedDifference_sq_eq_activity hpr hn
  rw [hrewrite]
  have hquad : (A - B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A + B)]
  calc
    (A - B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := hquad
    _ ≤ 2 * ((1 / 4 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q) +
              lowOwnerThresholdCrossingIndicator
                p (r * n) (rawQ2ChildCutoff R q)))) +
        2 * B ^ 2 := by nlinarith [hA]
    _ = (1 / 2 : ℝ) *
          (∑ q ∈ canonicalRoughLowQ2Owners R,
            (lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q) +
              lowOwnerThresholdCrossingIndicator
                p (r * n) (rawQ2ChildCutoff R q))) +
        2 *
          (lowOwnerThresholdCrossingIndicator p n (R - 1) +
            lowOwnerThresholdCrossingIndicator p (r * n) (R - 1)) := by
      rw [hB]
      ring


/-!
## Exact q²-threshold overlap census

For a fixed current owner \`p\`, each reciprocal daughter \`q\` contributes the
literal site window

  n <= Y_q < p*n,

where \`Y_q = floor(X_R/q^2)\`.  The daughter crossing weight is the reciprocal
superposition of these windows.  Its physical site L² energy is therefore
exactly the reciprocal weighted overlap census of the windows.  No Cauchy,
absolute value, or prime-spacing estimate is used.
-/

/-- Physical overlap mass of two literal q² threshold windows for one current
owner. -/
def lowOwnerDaughterThresholdWindowOverlapMass
    (R p q q' : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
    lowOwnerThresholdCrossingIndicator
        p n (rawQ2ChildCutoff R q) *
      lowOwnerThresholdCrossingIndicator
        p n (rawQ2ChildCutoff R q')

/-- **Exact reciprocal q² overlap Fubini.**

The diagonal physical site energy of the daughter crossing field is exactly
the weighted pairwise overlap census of its actual threshold windows. -/
theorem sum_lowOwnerDaughterCrossingWeight_sq_eq_overlapCensus
    (R p : ℕ) :
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
      lowOwnerDaughterCrossingWeight R p n ^ 2) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ q' ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) * ((1 : ℝ) / (q' : ℝ)) *
            lowOwnerDaughterThresholdWindowOverlapMass R p q q' := by
  simp_rw [lowOwnerDaughterCrossingWeight_eq_threshold_sum]
  unfold lowOwnerDaughterThresholdWindowOverlapMass
  simp_rw [pow_two]
  calc
    (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        (∑ q ∈ canonicalRoughLowQ2Owners R,
            ((1 : ℝ) / (q : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q)) *
          (∑ q' ∈ canonicalRoughLowQ2Owners R,
            ((1 : ℝ) / (q' : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q'))) =
      ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        ∑ q ∈ canonicalRoughLowQ2Owners R,
          ∑ q' ∈ canonicalRoughLowQ2Owners R,
            (((1 : ℝ) / (q : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q)) *
            (((1 : ℝ) / (q' : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q')) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.mul_sum]
    _ =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ q' ∈ canonicalRoughLowQ2Owners R,
          ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
            (((1 : ℝ) / (q : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q)) *
            (((1 : ℝ) / (q' : ℝ)) *
              lowOwnerThresholdCrossingIndicator
                p n (rawQ2ChildCutoff R q')) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_comm]
    _ =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        ∑ q' ∈ canonicalRoughLowQ2Owners R,
          ((1 : ℝ) / (q : ℝ)) * ((1 : ℝ) / (q' : ℝ)) *
            (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
              lowOwnerThresholdCrossingIndicator
                  p n (rawQ2ChildCutoff R q) *
                lowOwnerThresholdCrossingIndicator
                  p n (rawQ2ChildCutoff R q')) := by
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro q' _hq'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

end RHLean.Proof
