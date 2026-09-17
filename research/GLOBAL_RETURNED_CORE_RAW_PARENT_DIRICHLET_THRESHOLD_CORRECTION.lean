import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_DIRICHLET_INCIDENCE_GATE»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_CLIPPED_FUBINI»

/-!
# Dirichlet incidence = threshold incidence + exact endpoint correction

The completed-block currency bridge is not the whole story.  On the finite
physical clock the Dirichlet incidence differs from the threshold-potential
incidence by exactly one endpoint crossing indicator:

  D_p(n) = G_p(n) + chi_p(n; X_R).

This identity is valid for every natural site once `R >= 2` and `p >= 1`;
outside the physical clock all three terms vanish.  Taking one more owner
difference therefore gives

  Delta_r D_p(n)
    = Delta_r G_p(n)
      + [chi_p(n;X_R) - chi_p(r*n;X_R)].

By the already-compiled commuting-incidence identity, the bracket is exactly
`lowOwnerThresholdClippedDifference p r n X_R`.

Consequently every raw-parent Dirichlet incidence four-corner is an ordinary
threshold-incidence four-corner plus one explicit endpoint correction.  The
threshold term is in the existing reciprocal/Euler currency *without* a
completion assumption; the correction retains the entire physical cutoff.
No norm, square, or triangle inequality is introduced here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Universal one-edge currency identity.**  Physical Dirichlet incidence is
threshold incidence plus the literal endpoint crossing. -/
theorem lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointCrossing
    {R p n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p) :
    lowOwnerPhysicalDirichletIncidenceWeight R p n =
      lowOwnerThresholdOwnerIncidenceWeight R p n +
        lowOwnerThresholdCrossingIndicator p n (squareRootEndpoint R) := by
  by_cases hn : n ≤ squareRootEndpoint R
  · by_cases hpn : p * n ≤ squareRootEndpoint R
    · rw [lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete
        hn hpn]
      have hnot : ¬ squareRootEndpoint R < p * n := Nat.not_lt_of_ge hpn
      simp [lowOwnerThresholdCrossingIndicator, hn, hnot]
    · have hpnOut : squareRootEndpoint R < p * n := Nat.lt_of_not_ge hpn
      unfold lowOwnerPhysicalDirichletIncidenceWeight
        lowOwnerThresholdOwnerIncidenceWeight
      rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le hn,
        lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hpnOut,
        lowOwnerThresholdPotential_eq_weight_sub_one,
        lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hpnOut]
      simp [lowOwnerThresholdCrossingIndicator, hn, hpnOut]
      ring
  · have hnOut : squareRootEndpoint R < n := Nat.lt_of_not_ge hn
    have hnp : n ≤ p * n := by
      calc
        n = 1 * n := by simp
        _ ≤ p * n := Nat.mul_le_mul_right n hp
    have hpnOut : squareRootEndpoint R < p * n := hnOut.trans_le hnp
    unfold lowOwnerPhysicalDirichletIncidenceWeight
      lowOwnerThresholdOwnerIncidenceWeight
    rw [lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hnOut,
      lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hpnOut,
      lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hnOut,
      lowOwnerThresholdPotential_eq_zero_of_endpoint_lt hR hpnOut]
    simp [lowOwnerThresholdCrossingIndicator, Nat.not_le_of_gt hnOut]

/-- **Universal second-owner currency identity.**  The only difference between
Dirichlet and threshold second incidences is the exact physical endpoint
clipped-difference atom. -/
theorem lowOwnerDirichletIncidenceOwnerDifference_eq_thresholdSecond_add_endpointClipped
    {R p r n : ℕ} (hR : 2 ≤ R) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    lowOwnerDirichletOwnerDifference r
        (lowOwnerPhysicalDirichletIncidenceWeight R p) n =
      lowOwnerThresholdSecondOwnerDifference R p r n +
        lowOwnerThresholdClippedDifference
          p r n (squareRootEndpoint R) := by
  unfold lowOwnerDirichletOwnerDifference
    lowOwnerThresholdSecondOwnerDifference
  rw [lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointCrossing
      hR hp,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_add_endpointCrossing
      hR hp]
  have hcomm :=
    lowOwnerThresholdCrossing_secondIncidence_comm
      (p := p) (r := r) (a := n) (y := squareRootEndpoint R) hp hr
  unfold lowOwnerThresholdClippedDifference at hcomm ⊢
  rw [hcomm]
  ring

/-- Endpoint correction carried by one raw parent after both coordinates are
expanded into threshold plus clipping currency. -/
def lowOwnerRawParentEndpointIncidenceCorrectionMass
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  postRootZeroTargetPairExcess parent *
    (lowOwnerThresholdClippedDifference
        p r parent.1 (squareRootEndpoint R) *
      lowOwnerThresholdSecondOwnerDifference R p r parent.2 +
     lowOwnerThresholdSecondOwnerDifference R p r parent.1 *
      lowOwnerThresholdClippedDifference
        p r parent.2 (squareRootEndpoint R) +
     lowOwnerThresholdClippedDifference
        p r parent.1 (squareRootEndpoint R) *
      lowOwnerThresholdClippedDifference
        p r parent.2 (squareRootEndpoint R))

/-- **Pointwise all-raw-parent bridge.**  The physical Dirichlet incidence
four-corner is the ordinary threshold four-corner plus the explicit endpoint
correction. -/
theorem lowOwnerRawParentDirichletIncidenceFourCornerMass_eq_threshold_add_endpointCorrection
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent =
      weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p)
          r parent.1 parent.2 +
        lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, _haBase, _hbBase, hra, hrb⟩
  unfold lowOwnerRawParentDirichletIncidenceFourCornerMass
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerPhysicalDirichletIncidenceWeight R p) hr hra hrb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb,
    lowOwnerDirichletIncidenceOwnerDifference_eq_thresholdSecond_add_endpointClipped
      hR hp.one_le hr.one_le,
    lowOwnerDirichletIncidenceOwnerDifference_eq_thresholdSecond_add_endpointClipped
      hR hp.one_le hr.one_le]
  unfold lowOwnerRawParentEndpointIncidenceCorrectionMass
  ring

/-- Threshold-incidence mass over all occurring raw parents.  Unlike the old
completed gate, this signed object needs no endpoint-completion hypothesis. -/
def lowOwnerFirstOwnerRawParentThresholdIncidenceMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
    weightedMoebiusFreshPrimeFourCornerMass
      (lowOwnerThresholdOwnerIncidenceWeight R p)
      r parent.1 parent.2

/-- Aggregate exact endpoint correction over the same duplicate-free raw-parent
set. -/
def lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
    lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent

/-- Aggregate all-raw-parent Dirichlet/threshold bridge. -/
theorem lowOwnerFirstOwnerRawParentDirichletIncidenceMass_eq_threshold_add_endpointCorrection
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerRawParentDirichletIncidenceMass R p sig r =
      lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r +
        lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass
          R p sig r := by
  unfold lowOwnerFirstOwnerRawParentDirichletIncidenceMass
    lowOwnerFirstOwnerRawParentThresholdIncidenceMass
    lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro parent hparent
  exact
    lowOwnerRawParentDirichletIncidenceFourCornerMass_eq_threshold_add_endpointCorrection
      hR hp hparent

/-- **Universal threshold-gate signed splice.**  The entire raw-parent
next-polarization layer is now one threshold-incidence ledger, one exact
physical endpoint correction, and the still-signed same-branch continuation. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_threshold_add_endpointCorrection_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r +
        lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass
          R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r := by
  rw [sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_dirichletIncidence_sub_sameBranch
    hp]
  rw [lowOwnerFirstOwnerRawParentDirichletIncidenceMass_eq_threshold_add_endpointCorrection
    hR hp]
  ring

end RHLean.Proof
