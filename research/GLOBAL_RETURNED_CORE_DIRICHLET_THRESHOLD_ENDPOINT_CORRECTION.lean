import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_DIRICHLET_INCIDENCE_GATE»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»

/-!
# Exact endpoint correction from Dirichlet incidence to threshold incidence

The threshold potential differs from the physical Dirichlet extension only at
one place: a physical parent whose `p`-child has crossed beyond the square-root
endpoint.  Pointwise,

  I_D(p,n) = I_T(p,n) + chi_p(n, X_R),

where `chi_p(n,X_R)=1_{n <= X_R < p*n}`.

Taking the next-owner `r` difference gives

  Delta_r I_D(p,n)
    = Delta_r I_T(p,n)
      + (chi_p(n,X_R) - chi_p(r*n,X_R)).

By the already-compiled commutation of multiplicative incidences, the endpoint
correction is exactly `lowOwnerThresholdClippedDifference p r n X_R`.
Therefore the incomplete Dirichlet incidence is not a new analytic spectrum;
it is the ordinary threshold second difference plus one literal endpoint clip.

No inequality is used in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Endpoint clipping indicator for the current first-owner edge. -/
def lowOwnerDirichletEndpointClip
    (R p n : ℕ) : ℝ :=
  lowOwnerThresholdCrossingIndicator p n (squareRootEndpoint R)

/-- **Exact one-dimensional Dirichlet/threshold correction.** -/
theorem lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointClip
    {R p n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p) :
    lowOwnerPhysicalDirichletIncidenceWeight R p n =
      lowOwnerThresholdOwnerIncidenceWeight R p n +
        lowOwnerDirichletEndpointClip R p n := by
  let X := squareRootEndpoint R
  by_cases hn : n ≤ X
  · have hDn := lowOwnerPhysicalDirichletWeight_eq_weight_of_le hn
    by_cases hpn : p * n ≤ X
    · have hDpn := lowOwnerPhysicalDirichletWeight_eq_weight_of_le hpn
      have hcross : lowOwnerDirichletEndpointClip R p n = 0 := by
        unfold lowOwnerDirichletEndpointClip lowOwnerThresholdCrossingIndicator X
        simp [hn, Nat.not_lt_of_ge hpn]
      unfold lowOwnerPhysicalDirichletIncidenceWeight
        lowOwnerThresholdOwnerIncidenceWeight
      rw [hDn, hDpn,
        lowOwnerThresholdPotential_eq_weight_sub_one,
        lowOwnerThresholdPotential_eq_weight_sub_one,
        hcross]
      ring
    · have hpnlt : X < p * n := Nat.lt_of_not_ge hpn
      have hDpn := lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hpnlt
      have hTpn := lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hpnlt
      have hcross : lowOwnerDirichletEndpointClip R p n = 1 := by
        unfold lowOwnerDirichletEndpointClip lowOwnerThresholdCrossingIndicator X
        simp [hn, hpnlt]
      unfold lowOwnerPhysicalDirichletIncidenceWeight
        lowOwnerThresholdOwnerIncidenceWeight
      rw [hDn, hDpn,
        lowOwnerThresholdPotential_eq_weight_sub_one,
        hTpn, hcross]
      ring
  · have hnlt : X < n := Nat.lt_of_not_ge hn
    have hnp : n ≤ p * n := by
      calc
        n = 1 * n := by simp
        _ ≤ p * n := Nat.mul_le_mul_right n hp
    have hpnlt : X < p * n := hnlt.trans_le hnp
    have hDn := lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hnlt
    have hDpn := lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hpnlt
    have hTn := lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hnlt
    have hTpn := lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hpnlt
    have hcross : lowOwnerDirichletEndpointClip R p n = 0 := by
      unfold lowOwnerDirichletEndpointClip lowOwnerThresholdCrossingIndicator X
      simp [hn]
    unfold lowOwnerPhysicalDirichletIncidenceWeight
      lowOwnerThresholdOwnerIncidenceWeight
    rw [hDn, hDpn, hTn, hTpn, hcross]
    ring

/-- **Exact next-owner correction.**  The `r`-difference of the physical
Dirichlet incidence is the threshold second-owner difference plus the literal
endpoint clipped-difference already used by the finite clipped Fubini. -/
theorem lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
    {R p r n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    lowOwnerDirichletOwnerDifference r
        (lowOwnerPhysicalDirichletIncidenceWeight R p) n =
      lowOwnerThresholdSecondOwnerDifference R p r n +
        lowOwnerThresholdClippedDifference
          p r n (squareRootEndpoint R) := by
  unfold lowOwnerDirichletOwnerDifference
    lowOwnerThresholdSecondOwnerDifference
  rw [lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointClip
      hR hp,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointClip
      hR hp]
  unfold lowOwnerDirichletEndpointClip lowOwnerThresholdClippedDifference
  rw [← lowOwnerThresholdCrossing_secondIncidence_comm hp hr]
  ring

/-- The raw-parent Dirichlet incidence four-corner is therefore the product of
`threshold second difference + endpoint clip correction` in the two parent
coordinates. -/
theorem lowOwnerRawParentDirichletIncidenceFourCornerMass_eq_thresholdPlusEndpointProduct
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent =
      postRootZeroTargetPairExcess parent *
        (lowOwnerThresholdSecondOwnerDifference R p r parent.1 +
          lowOwnerThresholdClippedDifference
            p r parent.1 (squareRootEndpoint R)) *
        (lowOwnerThresholdSecondOwnerDifference R p r parent.2 +
          lowOwnerThresholdClippedDifference
            p r parent.2 (squareRootEndpoint R)) := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hrPrime, _hpr, _haBase, _hbBase, hra, hrb⟩
  unfold lowOwnerRawParentDirichletIncidenceFourCornerMass
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerPhysicalDirichletIncidenceWeight R p) hrPrime hra hrb]
  rw [lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hrPrime.one_le,
    lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hrPrime.one_le]

end RHLean.Proof
