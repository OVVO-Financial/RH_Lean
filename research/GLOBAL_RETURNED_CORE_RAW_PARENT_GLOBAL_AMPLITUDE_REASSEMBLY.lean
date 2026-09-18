import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INCIDENCE_AMPLITUDE_FUBINI»
import «research.GLOBAL_RETURNED_CORE_INHERITED_MIXED_CLOCK_L2»

/-!
# Global signed branch amplitude reassembly and the exact crossing census

The revealed-signature fibres introduced by the raw-parent square realization
are a partition of the literal r-free branch.  Before any further square is
taken we can therefore collapse the fibre amplitudes back to one signed branch
amplitude.

This file also attaches the already-compiled deterministic mixed-clock L2
census to the *same* physical branch carrier.  It deliberately does not assert
the false inequality

  (sum on a fibre)^2 <= sum of site squares.

Thus the file records exactly what crossing counting buys after #754/#755 and
where signed amplitude reassembly is still required.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The whole signed clipped-difference amplitude on one r-free first-owner
branch, with no revealed-signature square inserted. -/
def lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
    (R p : ℕ) (sig : Finset ℕ) (r cutoff : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r,
    realMoebiusStep n *
      lowOwnerThresholdClippedDifference p r n cutoff

/-- The whole signed physical Dirichlet-incidence r-difference amplitude on the
same branch. -/
def lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r,
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n

/-- Revealed-signature Fubini for an arbitrary scalar site weight on the branch. -/
private theorem sum_branchSignatureFibers_eq_branch
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (f : ℕ → ℝ) :
    (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
      ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        f n) =
      ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r, f n := by
  let S := lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r
  let T := lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r
  let key : ℕ → Finset ℕ := lowOwnerRawParentRevealedKey R r
  have hmaps : ∀ n ∈ S, key n ∈ T := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := T) (g := key) hmaps f
  simpa [S, T, key,
    lowOwnerFirstOwnerRawParentBranchSignatureSet,
    lowOwnerFirstOwnerRawParentBranchSignatureFiber] using hfiber

/-- **Pre-square tau collapse for every clipped threshold.** -/
theorem sum_lowOwnerFirstOwnerBranchClippedDifferenceAmplitude_eq_total
    (R p : ℕ) (sig : Finset ℕ) (r cutoff : ℕ) :
    (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
      lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
        R p sig tau r cutoff) =
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r cutoff := by
  unfold lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
    lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
  exact sum_branchSignatureFibers_eq_branch R p sig r
    (fun n =>
      realMoebiusStep n *
        lowOwnerThresholdClippedDifference p r n cutoff)

/-- **Pre-square tau collapse for the physical incidence amplitude.** -/
theorem sum_lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_total
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r) =
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
        R p sig r := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
  exact sum_branchSignatureFibers_eq_branch R p sig r
    (lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r)

/-- Finite Fubini for the q-synthesis on one already-reassembled branch. -/
private theorem sum_branch_mul_ownerSum_eq_ownerSum_mul_sum
    (S Q : Finset ℕ) (a c : ℕ → ℝ) (d : ℕ → ℕ → ℝ) :
    (∑ n ∈ S, a n * (∑ q ∈ Q, c q * d q n)) =
      ∑ q ∈ Q, c q * (∑ n ∈ S, a n * d q n) := by
  calc
    (∑ n ∈ S, a n * (∑ q ∈ Q, c q * d q n)) =
        ∑ n ∈ S, ∑ q ∈ Q, a n * (c q * d q n) := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [Finset.mul_sum]
    _ = ∑ q ∈ Q, ∑ n ∈ S, a n * (c q * d q n) := by
          rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, c q * (∑ n ∈ S, a n * d q n) := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _hn
          ring

/-- **Whole-branch clipped Fubini before squaring.**

This is the #755 identity after the artificial revealed-signature labels have
been summed away.  The q-sum is outside the literal signed physical branch. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude_eq_clippedFubini
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
        R p sig r =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
            R p sig r (rawQ2ChildCutoff R q)) -
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r (R - 1) +
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r (squareRootEndpoint R) := by
  let S := lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
    lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
  change (∑ n ∈ S,
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n) = _
  calc
    (∑ n ∈ S,
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n) =
        ∑ n ∈ S,
          realMoebiusStep n *
            ((∑ q ∈ canonicalRoughLowQ2Owners R,
                (1 / (q : ℝ)) *
                  lowOwnerThresholdClippedDifference
                    p r n (rawQ2ChildCutoff R q)) -
              lowOwnerThresholdClippedDifference p r n (R - 1) +
              lowOwnerThresholdClippedDifference
                p r n (squareRootEndpoint R)) := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact
            lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_clippedFubini
              hR hp hr
    _ =
        ∑ n ∈ S,
          (realMoebiusStep n *
              (∑ q ∈ canonicalRoughLowQ2Owners R,
                (1 / (q : ℝ)) *
                  lowOwnerThresholdClippedDifference
                    p r n (rawQ2ChildCutoff R q)) -
            realMoebiusStep n *
              lowOwnerThresholdClippedDifference p r n (R - 1) +
            realMoebiusStep n *
              lowOwnerThresholdClippedDifference
                p r n (squareRootEndpoint R)) := by
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ =
        (∑ n ∈ S,
          realMoebiusStep n *
            (∑ q ∈ canonicalRoughLowQ2Owners R,
              (1 / (q : ℝ)) *
                lowOwnerThresholdClippedDifference
                  p r n (rawQ2ChildCutoff R q))) -
        (∑ n ∈ S,
          realMoebiusStep n *
            lowOwnerThresholdClippedDifference p r n (R - 1)) +
        (∑ n ∈ S,
          realMoebiusStep n *
            lowOwnerThresholdClippedDifference
              p r n (squareRootEndpoint R)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ =
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (1 / (q : ℝ)) *
            (∑ n ∈ S,
              realMoebiusStep n *
                lowOwnerThresholdClippedDifference
                  p r n (rawQ2ChildCutoff R q))) -
        (∑ n ∈ S,
          realMoebiusStep n *
            lowOwnerThresholdClippedDifference p r n (R - 1)) +
        (∑ n ∈ S,
          realMoebiusStep n *
            lowOwnerThresholdClippedDifference
              p r n (squareRootEndpoint R)) := by
          rw [sum_branch_mul_ownerSum_eq_ownerSum_mul_sum]
    _ = _ := by rfl

/-- Branch sites lie on the same physical common clock used by the global
mixed-clock census. -/
theorem lowOwnerFirstOwnerRawParentBranchSiteCarrier_subset_clock
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r ⊆
      Finset.Icc 1 (squareRootEndpoint R) := by
  intro n hn
  have hbase := (Finset.mem_filter.mp hn).1
  have hcar := (Finset.mem_filter.mp hbase).1
  exact (Finset.mem_filter.mp hcar).1

private theorem realMoebiusStep_sq_eq_one_of_branch
    {R p r n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r) :
    realMoebiusStep n ^ 2 = 1 := by
  have hbase := (Finset.mem_filter.mp hn).1
  have hcar := (Finset.mem_filter.mp hbase).1
  have hmu := (Finset.mem_filter.mp hcar).2
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h] at hmu ⊢

/-- On the actual branch carrier the signed threshold-site square is exactly
the deterministic second-incidence square. -/
theorem lowOwnerRawParentThresholdSignedSite_sq_eq_secondDifference_sq
    {R p r n : ℕ} {sig : Finset ℕ}
    (hn : n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r) :
    lowOwnerRawParentThresholdSignedSite R p r n ^ 2 =
      lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 := by
  unfold lowOwnerRawParentThresholdSignedSite
  rw [mul_pow, realMoebiusStep_sq_eq_one_of_branch hn]
  ring

/-- **The exact crossing census on the actual #754 branch carrier.**

This is a genuine root-square site-L2 bound.  It is intentionally a site
energy, not the square of a fibre sum. -/
theorem sum_lowOwnerRawParentThresholdSignedSite_sq_le_five_root_sq
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r,
      lowOwnerRawParentThresholdSignedSite R p r n ^ 2) ≤
      5 * (R : ℝ) ^ 2 := by
  have hsub :=
    lowOwnerFirstOwnerRawParentBranchSiteCarrier_subset_clock R p sig r
  calc
    (∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r,
      lowOwnerRawParentThresholdSignedSite R p r n ^ 2) =
        ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSiteCarrier R p sig r,
          lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 := by
            apply Finset.sum_congr rfl
            intro n hn
            exact
              lowOwnerRawParentThresholdSignedSite_sq_eq_secondDifference_sq hn
    _ ≤ ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
          lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (by
                intro n _hn _hnot
                exact sq_nonneg _)
    _ ≤ 5 * (R : ℝ) ^ 2 :=
      sum_lowOwnerThresholdSecondOwnerDifference_sq_le_five_root_sq
        hR hp hr hpr

end RHLean.Proof
