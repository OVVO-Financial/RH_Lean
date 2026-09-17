import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_SQUARES»

/-!
# Threshold branch amplitudes as complete r-orbit sums

The branch-square realization keeps the Möbius sign inside each revealed fibre.
For an r-free site `n`, squarefreeness gives the exact sign reversal

  mu(r*n) = -mu(n).

Hence the signed second-owner threshold site is not an unrelated finite
difference:

  mu(n) * (g_p(n) - g_p(r*n))
    = mu(n) g_p(n) + mu(r*n) g_p(r*n).

Thus every branch-fibre amplitude is a sum of complete two-point r-orbits.  If
the r-child leaves the physical clock, the second orbit endpoint vanishes
exactly by the threshold Dirichlet boundary theorem.  No magnitude estimate is
introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed current-p threshold-incidence site before the next-owner difference. -/
def lowOwnerThresholdOwnerSignedSite
    (R p n : ℕ) : ℝ :=
  realMoebiusStep n * lowOwnerThresholdOwnerIncidenceWeight R p n

/-- **Pointwise r-orbit completion.** -/
theorem lowOwnerRawParentThresholdSignedSite_eq_ownerOrbit
    {R p r n : ℕ}
    (hr : r.Prime) (hrn : ¬ r ∣ n) :
    lowOwnerRawParentThresholdSignedSite R p r n =
      lowOwnerThresholdOwnerSignedSite R p n +
        lowOwnerThresholdOwnerSignedSite R p (r * n) := by
  unfold lowOwnerRawParentThresholdSignedSite
    lowOwnerThresholdSecondOwnerDifference
    lowOwnerThresholdOwnerSignedSite
  rw [realMoebiusStep_mul_prime_eq_neg hr hrn]
  ring

/-- If the r-child is outside the physical clock, its threshold-incidence site
vanishes exactly. -/
theorem lowOwnerThresholdOwnerSignedSite_eq_zero_of_endpoint_lt
    {R p n : ℕ}
    (hR : 2 ≤ R) (hp : 1 ≤ p)
    (hn : squareRootEndpoint R < n) :
    lowOwnerThresholdOwnerSignedSite R p n = 0 := by
  unfold lowOwnerThresholdOwnerSignedSite
  rw [lowOwnerThresholdOwnerIncidenceWeight_eq_zero_of_next_clipped
    (R := R) (p := p) (r := 1) (n := n) hR hp]
  · ring
  · simpa using hn

/-- On an r-free branch fibre every signed second-difference site is literally
its two-point r-orbit sum. -/
theorem lowOwnerFirstOwnerRawParentBranchThresholdAmplitude_eq_sum_ownerOrbits
    {R p r : ℕ} {sig tau : Finset ℕ}
    (hr : r.Prime) :
    lowOwnerFirstOwnerRawParentBranchThresholdAmplitude R p sig tau r =
      ∑ n ∈ lowOwnerFirstOwnerRawParentBranchSignatureFiber R p sig tau r,
        (lowOwnerThresholdOwnerSignedSite R p n +
          lowOwnerThresholdOwnerSignedSite R p (r * n)) := by
  unfold lowOwnerFirstOwnerRawParentBranchThresholdAmplitude
  apply Finset.sum_congr rfl
  intro n hn
  have hbranch := (Finset.mem_filter.mp hn).1
  have hrFree := (Finset.mem_filter.mp hbranch).2
  exact lowOwnerRawParentThresholdSignedSite_eq_ownerOrbit hr hrFree

/-- The same identity on the tail collapses to the parent endpoint only, since
all r-children there lie beyond the physical clock. -/
theorem lowOwnerFirstOwnerRawParentTailThresholdAmplitude_eq_parentSum
    {R p r : ℕ} {sig tau : Finset ℕ}
    (hR : 2 ≤ R) (hp : 1 ≤ p) (hr : r.Prime) :
    lowOwnerFirstOwnerRawParentTailThresholdAmplitude R p sig tau r =
      ∑ n ∈ lowOwnerFirstOwnerRawParentTailSignatureFiber R p sig tau r,
        lowOwnerThresholdOwnerSignedSite R p n := by
  unfold lowOwnerFirstOwnerRawParentTailThresholdAmplitude
  apply Finset.sum_congr rfl
  intro n hn
  have htail := (Finset.mem_filter.mp hn).1
  have htailSite := (Finset.mem_filter.mp htail).1
  have hrFree := (Finset.mem_filter.mp htailSite).2
  have hrOut := (Finset.mem_filter.mp htail).2
  have horbit := lowOwnerRawParentThresholdSignedSite_eq_ownerOrbit
    (R := R) (p := p) hr hrFree
  have hzero := lowOwnerThresholdOwnerSignedSite_eq_zero_of_endpoint_lt
    (R := R) (p := p) hR hp hrOut
  rw [horbit, hzero]
  ring

end RHLean.Proof
