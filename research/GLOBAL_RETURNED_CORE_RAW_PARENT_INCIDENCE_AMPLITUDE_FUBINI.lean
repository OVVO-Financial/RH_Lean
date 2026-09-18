import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_CROSS_AMPLITUDE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_THRESHOLD_ENDPOINT_CORRECTION»

/-!
# Telescope the assembled raw-parent incidence amplitude before squaring

PR #754 completed every current-owner raw-parent orbit by virtual Dirichlet-zero
corners and then reassembled the full revealed branch before introducing the
first positive estimate.  The resulting gate is

  current signed polarization
    <= (1/2) * sum_tau |Delta_r I_D|_tau^2,

where each fibre amplitude is still signed.

This file now pushes the already-compiled clipped Fubini identity through that
assembled fibre amplitude before the square is taken.  Thus each Dirichlet
incidence amplitude is exactly

  q^2 daughter synthesis - root clip + physical endpoint clip.

The q-sum is outside the physical n-sum.  This is the form needed by the
existing reciprocal-square Perron/Basel frame.  No Cauchy--Schwarz, triangle
inequality, norm estimate, or new arithmetic hypothesis is used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed clipped-difference amplitude on one revealed branch fibre. -/
def lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
    (R p : ℕ) (sig tau : Finset ℕ) (r cutoff : ℕ) : ℝ :=
  ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
    realMoebiusStep n *
      lowOwnerThresholdClippedDifference p r n cutoff

/-- Fubini for a finite scalar synthesis: the owner sum may be moved outside
an already-assembled physical fibre without taking a magnitude. -/
private theorem sum_mul_ownerSum_eq_ownerSum_mul_sum
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

/-- Pointwise Dirichlet incidence difference in exact clipped-Fubini currency. -/
theorem lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_clippedFubini
    {R p r n : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n =
      realMoebiusStep n *
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℝ)) *
              lowOwnerThresholdClippedDifference
                p r n (rawQ2ChildCutoff R q)) -
          lowOwnerThresholdClippedDifference p r n (R - 1) +
          lowOwnerThresholdClippedDifference
            p r n (squareRootEndpoint R)) := by
  have hR1 : 1 ≤ R := by omega
  unfold lowOwnerBranchDirichletIncidenceDifferenceSignedSite
  rw [lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hr.one_le,
    lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
      hR1 hp.one_le hr.one_le]
  ring

/-- **Amplitude-level clipped Fubini.**  The q-synthesis is moved outside the
physical branch fibre before any square is taken. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_clippedFubini
    {R p r : ℕ} {sig tau : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
        R p sig tau r =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
            R p sig tau r (rawQ2ChildCutoff R q)) -
      lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
        R p sig tau r (R - 1) +
      lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
        R p sig tau r (squareRootEndpoint R) := by
  let S := lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r
  have hpoint :
      ∀ n ∈ S,
        lowOwnerBranchDirichletIncidenceDifferenceSignedSite R p r n =
          realMoebiusStep n *
            ((∑ q ∈ canonicalRoughLowQ2Owners R,
                (1 / (q : ℝ)) *
                  lowOwnerThresholdClippedDifference
                    p r n (rawQ2ChildCutoff R q)) -
              lowOwnerThresholdClippedDifference p r n (R - 1) +
              lowOwnerThresholdClippedDifference
                p r n (squareRootEndpoint R)) := by
    intro n _hn
    exact
      lowOwnerBranchDirichletIncidenceDifferenceSignedSite_eq_clippedFubini
        hR hp hr
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude
    lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
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
          intro n hn
          exact hpoint n hn
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
          apply congrArg (fun x : ℝ => x)
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro n _hn
          ring
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
          rw [sum_mul_ownerSum_eq_ownerSum_mul_sum]
    _ = _ := by rfl

/-- The assembled positive incidence energy is now literally a sum of squares
of the pre-square clipped-Fubini synthesis. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_clippedFubini
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy R p sig r =
      ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℝ)) *
              lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
                R p sig tau r (rawQ2ChildCutoff R q)) -
          lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
            R p sig tau r (R - 1) +
          lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
            R p sig tau r (squareRootEndpoint R)) ^ 2 := by
  unfold lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy
  apply Finset.sum_congr rfl
  intro tau _htau
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceAmplitude_eq_clippedFubini
    hR hp hr]

/-- **Post-#754 pre-square gate.**  The complete current-owner polarization is
controlled by one half of a sum of squares only after the reciprocal q-synthesis
has been exposed at amplitude level. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_half_clippedFubiniEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      (1 / 2 : ℝ) *
        ∑ tau ∈ lowOwnerFirstOwnerRawParentBranchSignatureSet R p sig r,
          ((∑ q ∈ canonicalRoughLowQ2Owners R,
              (1 / (q : ℝ)) *
                lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
                  R p sig tau r (rawQ2ChildCutoff R q)) -
            lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
              R p sig tau r (R - 1) +
            lowOwnerFirstOwnerBranchClippedDifferenceAmplitude
              R p sig tau r (squareRootEndpoint R)) ^ 2 := by
  have hgate :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_half_dirichletIncidenceEnergy
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  rw [lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceEnergy_eq_clippedFubini
    hR hp hr] at hgate
  exact hgate

end RHLean.Proof
