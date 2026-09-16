import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_FOUR_CORNER_ENERGY_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_OWNER_CUBE»

/-!
# Completed Dirichlet polarization before energy

The signed rank induction does not recurse on the square of one incidence
four-corner.  Its exact local state is the Dirichlet polarization

  Pi = incidence*incidence - base*base - returned*returned.

On a completed owner block all relevant p-edges are physical, so the incidence
owner difference is exactly the threshold second-owner difference.  This file
therefore exposes the completed block as an exact signed difference of three
fresh-owner four-corner masses:

  completed Pi block
    = threshold-incidence four-corner
      - base four-corner
      - returned-child four-corner.

Only the first term has already been identified, after squaring, with the
owner-labelled reciprocal energy carrying the `2/9` contraction.  The last two
terms remain signed here.  They must be telescoped/classified before any energy
estimate is applied.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- On a completed r-block, the r-difference of the Dirichlet p-incidence is
literally the threshold second-owner difference. -/
theorem lowOwnerDirichletIncidence_ownerDifference_eq_thresholdSecond_of_complete
    {R p r n : ℕ}
    (hn : n ≤ squareRootEndpoint R)
    (hpn : p * n ≤ squareRootEndpoint R)
    (hrn : r * n ≤ squareRootEndpoint R)
    (hprn : p * (r * n) ≤ squareRootEndpoint R) :
    lowOwnerDirichletOwnerDifference r
        (lowOwnerDirichletIncidenceCoefficient R p) n =
      lowOwnerThresholdSecondOwnerDifference R p r n := by
  change
    lowOwnerPhysicalDirichletIncidenceWeight R p n -
        lowOwnerPhysicalDirichletIncidenceWeight R p (r * n) =
      lowOwnerThresholdOwnerIncidenceWeight R p n -
        lowOwnerThresholdOwnerIncidenceWeight R p (r * n)
  rw [lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete hn hpn,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete hrn hprn]

/-- The next Dirichlet polarization scalar, on a completed block, has the
threshold-incidence product as its first term and retains the two signed
same-branch owner differences exactly. -/
theorem lowOwnerDirichletNextPolarizationScalar_eq_threshold_sub_branches_of_complete
    {R p r a b : ℕ}
    (ha : a ≤ squareRootEndpoint R)
    (hpa : p * a ≤ squareRootEndpoint R)
    (hra : r * a ≤ squareRootEndpoint R)
    (hpra : p * (r * a) ≤ squareRootEndpoint R)
    (hb : b ≤ squareRootEndpoint R)
    (hpb : p * b ≤ squareRootEndpoint R)
    (hrb : r * b ≤ squareRootEndpoint R)
    (hprb : p * (r * b) ≤ squareRootEndpoint R) :
    lowOwnerDirichletNextPolarizationScalar R p r a b =
      lowOwnerThresholdSecondOwnerDifference R p r a *
          lowOwnerThresholdSecondOwnerDifference R p r b -
        lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletBaseCoefficient R) a *
          lowOwnerDirichletOwnerDifference r
            (lowOwnerDirichletBaseCoefficient R) b -
        lowOwnerDirichletOwnerDifference r
          (lowOwnerDirichletReturnedCoefficient R p) a *
          lowOwnerDirichletOwnerDifference r
            (lowOwnerDirichletReturnedCoefficient R p) b := by
  unfold lowOwnerDirichletNextPolarizationScalar
  rw [lowOwnerDirichletIncidence_ownerDifference_eq_thresholdSecond_of_complete
      ha hpa hra hpra,
    lowOwnerDirichletIncidence_ownerDifference_eq_thresholdSecond_of_complete
      hb hpb hrb hprb]

/-- **Exact completed-block signed currency decomposition.**

The full four-corner Dirichlet polarization is the threshold-incidence
four-corner minus the base and returned-child four-corners.  This is an equality
of signed masses, not an energy estimate. -/
theorem lowOwnerDirichletPolarization_fourCorner_eq_threshold_sub_branchFourCorners_of_complete
    {R p r a b : ℕ}
    (hr : r.Prime) (hraFresh : ¬ r ∣ a) (hrbFresh : ¬ r ∣ b)
    (ha : a ≤ squareRootEndpoint R)
    (hpa : p * a ≤ squareRootEndpoint R)
    (hra : r * a ≤ squareRootEndpoint R)
    (hpra : p * (r * a) ≤ squareRootEndpoint R)
    (hb : b ≤ squareRootEndpoint R)
    (hpb : p * b ≤ squareRootEndpoint R)
    (hrb : r * b ≤ squareRootEndpoint R)
    (hprb : p * (r * b) ≤ squareRootEndpoint R) :
    lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, b) +
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, b) +
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (a, r * b) +
        lowOwnerFirstOwnerDirichletPolarizationAtom R p (r * a, r * b) =
      weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b -
        weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerDirichletBaseCoefficient R) r a b -
        weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerDirichletReturnedCoefficient R p) r a b := by
  rw [lowOwnerDirichletPolarization_fourCorner_eq_nextPolarization
    hr hraFresh hrbFresh]
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerThresholdOwnerIncidenceWeight R p) hr hraFresh hrbFresh,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerDirichletBaseCoefficient R) hr hraFresh hrbFresh,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerDirichletReturnedCoefficient R p) hr hraFresh hrbFresh]
  rw [lowOwnerDirichletNextPolarizationScalar_eq_threshold_sub_branches_of_complete
    ha hpa hra hpra hb hpb hrb hprb]
  unfold lowOwnerThresholdSecondOwnerDifference
  simp only [postRootZeroTargetPairExcess_eq_weight]
  ring

end RHLean.Proof
