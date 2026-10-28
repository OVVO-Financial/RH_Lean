import Mathlib
import «research.EULER_THREE_STRATUM_SQUARE_SAMPLING_20261028»

/-!
# Two-stage surrogate randomness: location strata and Euler prime-owner strata

Sample the *deterministic* integer index R uniformly over H <= R < 2H,
then apply two R-dependent partitions to the same original Mobius prefix:

 (A) physical integer location: [1,R-1], (R-1,X_R/2], (X_R/2,X_R];
 (B) greatest admitted prime: p<R, R<=p<=X_R/2, p>X_R/2.

These ARE NOT the same three partitions. The physical top half contains
composites; the prime-owner top class consists solely of prime singletons.
All masks change when R changes. No independent signs are inserted.

Every square-shell increment is recovered by either mask system; expanding
their product yields the original coupled NINE-channel signed sampler.
A stochastic-looking model or empirical covariance is not a number-theoretic
power-saving bound. The latter is left OPEN.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- Site-location stratum 1: the literal integer prefix below sqrt(X_R). -/
def eulerSiteLow (R : ℕ) : ℂ :=
  mertensSummatory (R - 1)

/-- Site-location stratum 2: site integers R <= n <= floor(X_R/2). -/
def eulerSiteMiddle (R : ℕ) : ℂ :=
  mertensSummatory (squareRootEndpoint R / 2) -
    mertensSummatory (R - 1)

/-- Site-location stratum 3: site integers floor(X_R/2) < n <= X_R.
This contains BOTH prime and composite integers. -/
def eulerSiteTop (R : ℕ) : ℂ :=
  mertensSummatory (squareRootEndpoint R) -
    mertensSummatory (squareRootEndpoint R / 2)

/-- Source-faithful literal location partition; no Euler prime-owner assumption. -/
theorem eulerSite_endpoint_eq_three_location_strata (R : ℕ) :
    mertensSummatory (squareRootEndpoint R) =
      eulerSiteLow R + eulerSiteMiddle R + eulerSiteTop R := by
  unfold eulerSiteLow eulerSiteMiddle eulerSiteTop
  ring

/-- The two three-band partitions are independent coordinate descriptions
of the SAME deterministic signed endpoint. They are not statistically
independent samples. -/
theorem eulerSite_eq_primeOwner_partition
    (R : ℕ) (hR : 2 ≤ R) :
    eulerSiteLow R + eulerSiteMiddle R + eulerSiteTop R =
      eulerThreeLow R + eulerThreeMiddle R + eulerThreeTop R := by
  rw [← eulerSite_endpoint_eq_three_location_strata,
      ← eulerThree_endpoint_eq_three_strata R hR]

/-- Signed flux through the literal small-site location band when R advances. -/
def eulerSiteShellLow (R : ℕ) : ℝ :=
  (eulerSiteLow (R + 1) - eulerSiteLow R).re

/-- Signed flux through the moving square-root to half-X site band. -/
def eulerSiteShellMiddle (R : ℕ) : ℝ :=
  (eulerSiteMiddle (R + 1) - eulerSiteMiddle R).re

/-- Signed flux through the moving upper-half site band, including composites. -/
def eulerSiteShellTop (R : ℕ) : ℝ :=
  (eulerSiteTop (R + 1) - eulerSiteTop R).re

/-- Every moving location partition has its gate-switch charge, but its
COMPLETE signed flux is exactly the genuine square-shell Mobius increment. -/
theorem eulerSite_shellFlow_eq_three (R : ℕ) :
    eulerThreeShellMobius R =
      eulerSiteShellLow R + eulerSiteShellMiddle R +
        eulerSiteShellTop R := by
  unfold eulerThreeShellMobius eulerSiteShellLow
    eulerSiteShellMiddle eulerSiteShellTop
    eulerSiteLow eulerSiteMiddle eulerSiteTop
  simp only [Complex.sub_re]
  ring

/-- Exact six-term Gram under square-root index sampling using the
moving literal *integer-location* bands. -/
theorem eulerSite_sampledSixTermGram
    (H : ℕ) :
    eulerThreeSampledShellEnergy H =
      (∑ R ∈ Finset.Ico H (2 * H), (eulerSiteShellLow R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H), (eulerSiteShellMiddle R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H), (eulerSiteShellTop R) ^ 2) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerSiteShellLow R * eulerSiteShellMiddle R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerSiteShellLow R * eulerSiteShellTop R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        2 * eulerSiteShellMiddle R * eulerSiteShellTop R) := by
  unfold eulerThreeSampledShellEnergy
  calc
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          (eulerSiteShellLow R + eulerSiteShellMiddle R +
            eulerSiteShellTop R) ^ 2 := by
      apply Finset.sum_congr rfl
      intro R _hR
      rw [eulerSite_shellFlow_eq_three]
    _ = ∑ R ∈ Finset.Ico H (2 * H),
          ((eulerSiteShellLow R) ^ 2 +
           (eulerSiteShellMiddle R) ^ 2 +
           (eulerSiteShellTop R) ^ 2 +
           2 * eulerSiteShellLow R * eulerSiteShellMiddle R +
           2 * eulerSiteShellLow R * eulerSiteShellTop R +
           2 * eulerSiteShellMiddle R * eulerSiteShellTop R) := by
      apply Finset.sum_congr rfl
      intro R _hR
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib]

/-- The genuine two-axis sampler: every site-band flux is multiplied by
every prime-owner-band flux at the SAME square-block index R. Retaining
these cross terms is mandatory; the masks need not be independent. -/
def eulerSiteOwnerSampledCross (H : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico H (2 * H),
    (eulerSiteShellLow R + eulerSiteShellMiddle R +
      eulerSiteShellTop R) *
    (eulerThreeShellLow R + eulerThreeShellMiddle R +
      eulerThreeShellTop R)

/-- Exact two-axis surrogate sampling identity. The total is still the
true square-shell energy; any saving needs NEW bounds on these correlations. -/
theorem eulerSiteOwnerSampledCross_eq_squareShellEnergy
    (H : ℕ) (hH : 2 ≤ H) :
    eulerSiteOwnerSampledCross H = eulerThreeSampledShellEnergy H := by
  unfold eulerSiteOwnerSampledCross eulerThreeSampledShellEnergy
  apply Finset.sum_congr rfl
  intro R hR
  have hR2 : 2 ≤ R := by
    have h := (Finset.mem_Ico.mp hR).1
    omega
  rw [← eulerSite_shellFlow_eq_three R,
      ← eulerThree_shellFlow_eq_three R hR2]
  ring

/-- Full NINE signed cross-correlations of the two deterministic sampling
partitions. In particular, this identity does not zero any mixed moment. -/
theorem eulerSiteOwnerSampledCross_eq_nine_terms (H : ℕ) :
    eulerSiteOwnerSampledCross H =
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellLow R * eulerThreeShellLow R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellLow R * eulerThreeShellMiddle R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellLow R * eulerThreeShellTop R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellMiddle R * eulerThreeShellLow R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellMiddle R * eulerThreeShellMiddle R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellMiddle R * eulerThreeShellTop R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellTop R * eulerThreeShellLow R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellTop R * eulerThreeShellMiddle R) +
      (∑ R ∈ Finset.Ico H (2 * H),
        eulerSiteShellTop R * eulerThreeShellTop R) := by
  unfold eulerSiteOwnerSampledCross
  calc
    _ = ∑ R ∈ Finset.Ico H (2 * H),
      (eulerSiteShellLow R * eulerThreeShellLow R +
       eulerSiteShellLow R * eulerThreeShellMiddle R +
       eulerSiteShellLow R * eulerThreeShellTop R +
       eulerSiteShellMiddle R * eulerThreeShellLow R +
       eulerSiteShellMiddle R * eulerThreeShellMiddle R +
       eulerSiteShellMiddle R * eulerThreeShellTop R +
       eulerSiteShellTop R * eulerThreeShellLow R +
       eulerSiteShellTop R * eulerThreeShellMiddle R +
       eulerSiteShellTop R * eulerThreeShellTop R) := by
      apply Finset.sum_congr rfl
      intro R _hR
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]

#print axioms eulerSite_endpoint_eq_three_location_strata
#print axioms eulerSite_eq_primeOwner_partition
#print axioms eulerSite_shellFlow_eq_three
#print axioms eulerSite_sampledSixTermGram
#print axioms eulerSiteOwnerSampledCross_eq_squareShellEnergy
#print axioms eulerSiteOwnerSampledCross_eq_nine_terms

end RHLean.Proof
