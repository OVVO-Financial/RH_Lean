import Mathlib
import «research.GLOBAL_RETURNED_CORE_GLOBAL_DESCENDING_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_GLOBAL_FIRST_OWNER_SITE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_MERTENS_WALL»
import «research.GLOBAL_RETURNED_CORE_POST755_AMPLITUDE_CLOSURE»
import «research.GLOBAL_RETURNED_CORE_INHERITED_DETERMINISTIC_CANCELLATION»

/-!
# Reciprocal q² threshold walls in one global descending pair coordinate

For a fixed wall owner r, assemble *all* low-q² threshold walls before taking
any pair product:

  V_{R,r}(n)
    = sum_q (1/q) * 1_{r-free}(n)
        * mu(n) * 1_{n <= Y_q < r*n}.

The one-dimensional signed mass of V is exactly the genuine reciprocal Mertens
column sum_q M(Y_q)/q.  Therefore its empty revealed-pair energy is the square
of that one amplitude, retaining every q != q' covariance term.

Applying the global greatest-owner Fubini charges every off-diagonal physical
pair exactly once.  Since the terminal diagonal is nonnegative, the whole
descending crossing ledger costs at most the empty energy, and the existing
quarter-frame estimate then gives a literal 1/4 q² daughter-energy budget.

No ownerwise square, coefficient-gradient estimate, or independence assumption
is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- One reciprocal q² threshold-wall synthesis, with the exposing wall owner's
divisible sites removed exactly as in the Mertens wall identity. -/
def lowOwnerReciprocalThresholdWallSignedSite
    (R r n : ℕ) : ℝ :=
  ∑ q ∈ canonicalRoughLowQ2Owners R,
    (1 / (q : ℝ)) *
      (if ¬ r ∣ n then
        realMoebiusStep n *
          lowOwnerThresholdCrossingIndicator
            r n (rawQ2ChildCutoff R q)
       else 0)

/-- Pointwise this is the r-free part of the already-defined daughter crossing
field, with the physical Mobius sign attached. -/
theorem lowOwnerReciprocalThresholdWallSignedSite_eq
    (R r n : ℕ) :
    lowOwnerReciprocalThresholdWallSignedSite R r n =
      if ¬ r ∣ n then
        lowOwnerDaughterCrossingWeight R r n * realMoebiusStep n
      else 0 := by
  unfold lowOwnerReciprocalThresholdWallSignedSite
  by_cases hrn : ¬ r ∣ n
  · simp only [hrn, if_true]
    rw [lowOwnerDaughterCrossingWeight_eq_threshold_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  · have hrd : r ∣ n := not_not.mp hrn
    simp [hrn, hrd]

/-- A fixed r-free threshold wall at cutoff y sums to the whole Mertens
amplitude M(y), even when evaluated on the common nonzero-Mobius clock. -/
theorem sum_nonzeroCarrier_rFree_thresholdCrossing_eq_mertens
    {R r y : ℕ} (hr : r.Prime)
    (hy : y ≤ squareRootEndpoint R) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      if ¬ r ∣ n then
        realMoebiusStep n *
          lowOwnerThresholdCrossingIndicator r n y
      else 0) =
      (mertensSummatoryInt y : ℝ) := by
  let X := squareRootEndpoint R
  let g : ℕ → ℝ := fun n =>
    if ¬ r ∣ n then
      realMoebiusStep n * lowOwnerThresholdCrossingIndicator r n y
    else 0
  have hremove :
      (∑ n ∈ lowOwnerNonzeroMobiusCarrier R, g n) =
        ∑ n ∈ Finset.Icc 1 X, g n := by
    unfold lowOwnerNonzeroMobiusCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hmu : realMoebiusStep n ≠ 0
    · simp [hmu, g]
    · have hz : realMoebiusStep n = 0 := not_ne_iff.mp hmu
      simp [hz, g]
  have hsub : Finset.Icc 1 y ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hny⟩
    exact Finset.mem_Icc.mpr ⟨hn1, hny.trans hy⟩
  have hzero :
      ∀ n ∈ Finset.Icc 1 X, n ∉ Finset.Icc 1 y → g n = 0 := by
    intro n hnX hny
    have hyn : y < n := by
      have hn1 := (Finset.mem_Icc.mp hnX).1
      by_contra hnot
      apply hny
      exact Finset.mem_Icc.mpr ⟨hn1, Nat.le_of_not_gt hnot⟩
    unfold g lowOwnerThresholdCrossingIndicator
    by_cases hdiv : r ∣ n
    · simp [hdiv]
    · have hnot : ¬ (n ≤ y ∧ y < r * n) := by omega
      simp [hdiv, hnot]
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      if ¬ r ∣ n then
        realMoebiusStep n *
          lowOwnerThresholdCrossingIndicator r n y
      else 0) =
        ∑ n ∈ lowOwnerNonzeroMobiusCarrier R, g n := by rfl
    _ = ∑ n ∈ Finset.Icc 1 X, g n := hremove
    _ = ∑ n ∈ Finset.Icc 1 y, g n :=
      (Finset.sum_subset hsub hzero).symm
    _ = (mertensSummatoryInt y : ℝ) := by
      unfold g
      exact sum_pFree_thresholdCrossing_eq_mertens hr

/-- **The whole synthesized wall site has exactly the reciprocal Mertens
column as its one-dimensional amplitude.** -/
theorem sum_lowOwnerReciprocalThresholdWallSignedSite_eq_column
    {R r : ℕ} (hr : r.Prime) :
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerReciprocalThresholdWallSignedSite R r n) =
      lowOwnerReciprocalMertensColumnReal R := by
  unfold lowOwnerReciprocalThresholdWallSignedSite
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (if ¬ r ∣ n then
            realMoebiusStep n *
              lowOwnerThresholdCrossingIndicator
                r n (rawQ2ChildCutoff R q)
           else 0)) =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
            if ¬ r ∣ n then
              realMoebiusStep n *
                lowOwnerThresholdCrossingIndicator
                  r n (rawQ2ChildCutoff R q)
            else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]
    _ =
      ∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (mertensSummatoryInt (rawQ2ChildCutoff R q) : ℝ) := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [sum_nonzeroCarrier_rFree_thresholdCrossing_eq_mertens hr]
        · rfl
        · unfold rawQ2ChildCutoff
          exact Nat.div_le_self _ _
    _ = lowOwnerReciprocalMertensColumnReal R := by
      rfl

/-- Empty revealed energy of the synthesized wall site is the square of the
literal reciprocal Mertens column. -/
theorem lowOwnerReciprocalThresholdWall_emptyEnergy_eq_column_sq
    {R r : ℕ} (hr : r.Prime) :
    lowOwnerRevealedPairMassWith R ∅
        (lowOwnerReciprocalThresholdWallSignedSite R r) =
      lowOwnerReciprocalMertensColumnReal R ^ 2 := by
  rw [lowOwnerRevealedPairMassWith_empty_eq_sum_sq]
  rw [sum_lowOwnerReciprocalThresholdWallSignedSite_eq_column hr]

/-- **Exact descending decomposition of the assembled q² wall Gram.**

All q=q' and q!=q' terms remain inside one site function. -/
theorem lowOwnerReciprocalThresholdWall_column_sq_eq_diagonal_add_descending
    {R r : ℕ} (hr : r.Prime) :
    lowOwnerReciprocalMertensColumnReal R ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith R
          (lowOwnerReciprocalThresholdWallSignedSite R r) +
        ∑ p ∈ primesUpTo (squareRootEndpoint R),
          lowOwnerRevealedCrossPairMassWith R
            (lowOwnerRevealedPrimesAbove R p) p
            (lowOwnerReciprocalThresholdWallSignedSite R r) := by
  rw [← lowOwnerReciprocalThresholdWall_emptyEnergy_eq_column_sq hr]
  exact
    lowOwnerRevealedPairMassWith_empty_eq_diagonal_add_descendingCross
      R (lowOwnerReciprocalThresholdWallSignedSite R r)

/-- The complete signed greatest-owner crossing ledger of the reciprocal q²
wall synthesis costs at most the square of the one assembled column. -/
theorem sum_lowOwnerReciprocalThresholdWall_descendingCross_le_column_sq
    {R r : ℕ} (hr : r.Prime) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerRevealedCrossPairMassWith R
        (lowOwnerRevealedPrimesAbove R p) p
        (lowOwnerReciprocalThresholdWallSignedSite R r)) ≤
      lowOwnerReciprocalMertensColumnReal R ^ 2 := by
  rw [← lowOwnerReciprocalThresholdWall_emptyEnergy_eq_column_sq hr]
  exact
    sum_lowOwnerDescendingCrossPairMassWith_le_emptyEnergy
      R (lowOwnerReciprocalThresholdWallSignedSite R r)

/-- **Quarter-energy global crossing bound.**

This is in the exact recursive q² Mertens-energy currency used by the final
consumer and retains every cross-q covariance term. -/
theorem sum_lowOwnerReciprocalThresholdWall_descendingCross_le_quarter_q2Energy
    {R r : ℕ} (hr : r.Prime) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerRevealedCrossPairMassWith R
        (lowOwnerRevealedPrimesAbove R p) p
        (lowOwnerReciprocalThresholdWallSignedSite R r)) ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  exact
    (sum_lowOwnerReciprocalThresholdWall_descendingCross_le_column_sq hr).trans
      (lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R)

/-- **Quarter-energy bound in the raw-parent outer coordinate.**

The same assembled reciprocal wall synthesis is now partitioned by the *least*
fresh owner.  This is the outer owner coordinate used by the raw-parent
chronology; every ordered off-diagonal pair is charged exactly once. -/
theorem sum_lowOwnerReciprocalThresholdWall_firstOwnerMass_le_quarter_q2Energy
    {R r : ℕ} (hr : r.Prime) :
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      lowOwnerGlobalFirstOwnerPairMassWith R p
        (lowOwnerReciprocalThresholdWallSignedSite R r)) ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R := by
  have hempty :=
    sum_lowOwnerGlobalFirstOwnerPairMassWith_le_emptyEnergy
      R (lowOwnerReciprocalThresholdWallSignedSite R r)
  rw [lowOwnerReciprocalThresholdWall_emptyEnergy_eq_column_sq hr] at hempty
  exact hempty.trans
    (lowOwnerReciprocalMertensColumnReal_sq_le_quarter_lowQ2DaughterEnergy R)

/-- The synthesized wall diagonal is deterministic and root-scale for each
exposing owner r. -/
theorem lowOwnerReciprocalThresholdWall_diagonal_le_sixteenth_endpoint
    (R r : ℕ) :
    lowOwnerGlobalDiagonalPairMassWith R
        (lowOwnerReciprocalThresholdWallSignedSite R r) ≤
      (1 / 16 : ℝ) * (squareRootEndpoint R : ℝ) := by
  rw [lowOwnerGlobalDiagonalPairMassWith_eq_sum_sq]
  have hsub :
      lowOwnerNonzeroMobiusCarrier R ⊆
        Finset.Icc 1 (squareRootEndpoint R) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hpoint :
      ∀ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerReciprocalThresholdWallSignedSite R r n ^ 2 ≤
          lowOwnerDaughterCrossingWeight R r n ^ 2 := by
    intro n hn
    rw [lowOwnerReciprocalThresholdWallSignedSite_eq]
    by_cases hfree : ¬ r ∣ n
    · rw [if_pos hfree]
      have hmu := (Finset.mem_filter.mp hn).2
      rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
        simp [realMoebiusStep, h] at hmu ⊢
    · rw [if_neg hfree]
      exact sq_nonneg _
  calc
    (∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
      lowOwnerReciprocalThresholdWallSignedSite R r n ^ 2) ≤
      ∑ n ∈ lowOwnerNonzeroMobiusCarrier R,
        lowOwnerDaughterCrossingWeight R r n ^ 2 := by
          exact Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerDaughterCrossingWeight R r n ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (by
              intro n _hn _hnot
              exact sq_nonneg _)
    _ ≤ (1 / 16 : ℝ) * (squareRootEndpoint R : ℝ) :=
      sum_lowOwnerDaughterCrossingWeight_sq_le_sixteenth_endpoint R r

end RHLean.Proof
