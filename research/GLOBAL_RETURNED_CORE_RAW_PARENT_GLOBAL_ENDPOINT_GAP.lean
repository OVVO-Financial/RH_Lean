import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_Q2_MERTENS_REASSEMBLY»
import «research.GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER»

/-!
# Global raw-parent incidence amplitude is the final Stokes endpoint gap

The #754/#755 raw-parent chronology can now be summed all the way through the
first-owner signature label before any square is taken.  Every clipped threshold
column has already been identified with the literal Mertens prefix at its
cutoff.  Consequently the entire branch incidence amplitude is exactly

  sum_q M(Y_q)/q - M(R-1) + M(X_R),

the negative of the all-endpoint Stokes/Mertens gap.

This is the desired one-amplitude identification: no raw-parent, revealed
signature, or first-owner bookkeeping remains.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Aggregate one-dimensional branch-incidence amplitude after removing the
lower-signature partition. -/
def lowOwnerGlobalBranchIncidenceDifferenceAmplitude
    (R p r : ℕ) : ℝ :=
  ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
    lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
      R p sig r

/-- Exact q² column in real scalar currency. -/
private theorem sum_signature_q2Column_eq_reciprocalMertensColumnReal
    {R p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ q ∈ canonicalRoughLowQ2Owners R,
      (1 / (q : ℝ)) *
        (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
            R p sig r (rawQ2ChildCutoff R q))) =
      lowOwnerReciprocalMertensColumnReal R := by
  unfold lowOwnerReciprocalMertensColumnReal
  apply Finset.sum_congr rfl
  intro q hq
  rw [sum_signature_branchQ2ClippedDifferenceTotalAmplitude_eq_mertensDaughter
    hp hr hpr]
  push_cast
  ring

/-- Root threshold after full signature reassembly is the literal Mertens
prefix M(R-1). -/
private theorem sum_signature_rootClipped_eq_mertens
    {R p r : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r (R - 1)) =
      (mertensSummatoryInt (R - 1) : ℝ) := by
  apply sum_signature_branchClippedDifferenceTotalAmplitude_eq_mertens
    hp hr hpr
  unfold squareRootEndpoint
  omega

/-- Endpoint threshold after full signature reassembly is the literal full-clock
Mertens prefix M(X_R). -/
private theorem sum_signature_endpointClipped_eq_mertens
    {R p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
        R p sig r (squareRootEndpoint R)) =
      (mertensSummatoryInt (squareRootEndpoint R) : ℝ) := by
  exact sum_signature_branchClippedDifferenceTotalAmplitude_eq_mertens
    hp hr hpr (le_rfl)

/-- **Global #755 amplitude normal form.**

After every signed finite Fubini/reassembly required by #754, the whole branch
incidence amplitude is exactly reciprocal q² daughters minus the two endpoint
Mertens values. -/
theorem lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_mertensGap
    {R p r : ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r =
      lowOwnerReciprocalMertensColumnReal R -
        (mertensSummatoryInt (R - 1) : ℝ) +
        (mertensSummatoryInt (squareRootEndpoint R) : ℝ) := by
  unfold lowOwnerGlobalBranchIncidenceDifferenceAmplitude
  calc
    (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude
        R p sig r) =
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ((∑ q ∈ canonicalRoughLowQ2Owners R,
            (1 / (q : ℝ)) *
              lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
                R p sig r (rawQ2ChildCutoff R q)) -
          lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
            R p sig r (R - 1) +
          lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
            R p sig r (squareRootEndpoint R)) := by
          apply Finset.sum_congr rfl
          intro sig _hsig
          exact
            lowOwnerFirstOwnerBranchDirichletIncidenceDifferenceTotalAmplitude_eq_clippedFubini
              hR hp hr
    _ =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
              R p sig r (rawQ2ChildCutoff R q))) -
      (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
          R p sig r (R - 1)) +
      (∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        lowOwnerFirstOwnerBranchClippedDifferenceTotalAmplitude
          R p sig r (squareRootEndpoint R)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_signature_q2Column_eq_reciprocalMertensColumnReal hp hr hpr,
        sum_signature_rootClipped_eq_mertens hR hp hr hpr,
        sum_signature_endpointClipped_eq_mertens hp hr hpr]

/-- The global #755 amplitude is independent of the auxiliary first/current
owner labels once their exact signed partitions are reassembled. -/
theorem lowOwnerGlobalBranchIncidenceDifferenceAmplitude_ownerIndependent
    {R p r p' r' : ℕ}
    (hR : 2 ≤ R)
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hp' : p'.Prime) (hr' : r'.Prime) (hpr' : p' < r') :
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p r =
      lowOwnerGlobalBranchIncidenceDifferenceAmplitude R p' r' := by
  rw [lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_mertensGap
      hR hp hr hpr,
    lowOwnerGlobalBranchIncidenceDifferenceAmplitude_eq_mertensGap
      hR hp' hr' hpr']

end RHLean.Proof
