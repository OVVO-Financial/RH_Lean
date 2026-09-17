import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_PREFIX_STAR»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_THRESHOLD_ENDPOINT_CORRECTION»

/-!
# Threshold incidence on the raw-parent prefix star

The intrinsic raw-parent carrier is a two-sided prefix star inside one revealed
branch.  The threshold four-corner itself is a product of the signed
one-dimensional site

  z_{p,r}(n) = mu(n) * Delta_r Delta_p F_R(n).

Therefore the whole raw-parent threshold-incidence ledger is not a generic
pair sum.  It is exactly the quadratic mass of the full revealed r-free branch
minus the quadratic mass of the tail where neither mixed r-child remains on
the physical clock.

This removes the pair-count multiplicity before any inequality is attempted.
No absolute value, norm, or Cauchy--Schwarz estimate is used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Full r-free same-revealed-branch carrier inside one first-owner cell. -/
def lowOwnerFirstOwnerRawParentBranchCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  ((lowOwnerFirstOwnerBaseFiber R p sig).product
      (lowOwnerFirstOwnerBaseFiber R p sig)).filter fun parent =>
    lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.1 =
      lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R r) parent.2 ∧
    ¬ r ∣ parent.1 ∧
    ¬ r ∣ parent.2

/-- Tail of that branch: neither mixed r-child is physical. -/
def lowOwnerFirstOwnerRawParentTailCarrier
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerRawParentBranchCarrier R p sig r).filter fun parent =>
    ¬ (r * parent.1 ≤ squareRootEndpoint R ∨
      r * parent.2 ≤ squareRootEndpoint R)

/-- The prefix star is exactly the complementary part of the full revealed
r-free branch. -/
theorem lowOwnerFirstOwnerRawParentPrefixStar_eq_branch_filter
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentPrefixStar R p sig r =
      (lowOwnerFirstOwnerRawParentBranchCarrier R p sig r).filter
        (fun parent =>
          r * parent.1 ≤ squareRootEndpoint R ∨
            r * parent.2 ≤ squareRootEndpoint R) := by
  ext parent
  simp [lowOwnerFirstOwnerRawParentPrefixStar,
    lowOwnerFirstOwnerRawParentBranchCarrier,
    and_assoc]

/-- Exact prefix/tail partition for an arbitrary signed pair weight. -/
theorem sum_lowOwnerFirstOwnerRawParentBranch_eq_prefix_add_tail
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerRawParentPrefixStar R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r,
        f parent := by
  rw [lowOwnerFirstOwnerRawParentPrefixStar_eq_branch_filter]
  unfold lowOwnerFirstOwnerRawParentTailCarrier
  exact Finset.sum_filter_add_sum_filter_not
    (s := lowOwnerFirstOwnerRawParentBranchCarrier R p sig r)
    (p := fun parent : ℕ × ℕ =>
      r * parent.1 ≤ squareRootEndpoint R ∨
        r * parent.2 ≤ squareRootEndpoint R)
    (f := f)

/-- Signed one-dimensional threshold second-incidence site. -/
def lowOwnerRawParentThresholdSignedSite
    (R p r n : ℕ) : ℝ :=
  realMoebiusStep n *
    lowOwnerThresholdSecondOwnerDifference R p r n

/-- A raw-parent threshold four-corner is exactly the product of its two signed
one-dimensional threshold sites. -/
theorem lowOwnerRawParentThresholdFourCorner_eq_siteProduct
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p)
        r parent.1 parent.2 =
      lowOwnerRawParentThresholdSignedSite R p r parent.1 *
        lowOwnerRawParentThresholdSignedSite R p r parent.2 := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, _haBase, _hbBase, hra, hrb⟩
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerRawParentThresholdSignedSite
  ring

/-- Quadratic threshold mass of the full revealed r-free branch. -/
def lowOwnerFirstOwnerRawParentBranchThresholdEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
    lowOwnerRawParentThresholdSignedSite R p r parent.1 *
      lowOwnerRawParentThresholdSignedSite R p r parent.2

/-- Quadratic threshold mass of the tail where both mixed r-children are
outside the physical clock. -/
def lowOwnerFirstOwnerRawParentTailThresholdEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerRawParentTailCarrier R p sig r,
    lowOwnerRawParentThresholdSignedSite R p r parent.1 *
      lowOwnerRawParentThresholdSignedSite R p r parent.2

/-- Raw-parent threshold mass rewritten on the intrinsic prefix-star carrier. -/
theorem lowOwnerFirstOwnerRawParentThresholdIncidenceMass_eq_prefixStarSiteProduct
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentPrefixStar R p sig r,
        lowOwnerRawParentThresholdSignedSite R p r parent.1 *
          lowOwnerRawParentThresholdSignedSite R p r parent.2 := by
  unfold lowOwnerFirstOwnerRawParentThresholdIncidenceMass
  rw [lowOwnerFirstOwnerPolarizationRawParentSet_eq_prefixStar hp hr hpr]
  apply Finset.sum_congr rfl
  intro parent hstar
  have hraw : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r := by
    rw [lowOwnerFirstOwnerPolarizationRawParentSet_eq_prefixStar hp hr hpr]
    exact hstar
  exact lowOwnerRawParentThresholdFourCorner_eq_siteProduct hp hraw

/-- **Prefix-star energy decrement.**  The entire signed threshold-incidence
ledger at owner r is the full revealed-branch quadratic mass minus the tail
quadratic mass. -/
theorem lowOwnerFirstOwnerRawParentThresholdIncidenceMass_eq_branchEnergy_sub_tailEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r -
        lowOwnerFirstOwnerRawParentTailThresholdEnergy R p sig r := by
  rw [lowOwnerFirstOwnerRawParentThresholdIncidenceMass_eq_prefixStarSiteProduct
    hp hr hpr]
  have hpartition :=
    sum_lowOwnerFirstOwnerRawParentBranch_eq_prefix_add_tail
      R p sig r
      (fun parent =>
        lowOwnerRawParentThresholdSignedSite R p r parent.1 *
          lowOwnerRawParentThresholdSignedSite R p r parent.2)
  unfold lowOwnerFirstOwnerRawParentBranchThresholdEnergy
    lowOwnerFirstOwnerRawParentTailThresholdEnergy at hpartition ⊢
  linarith

end RHLean.Proof
