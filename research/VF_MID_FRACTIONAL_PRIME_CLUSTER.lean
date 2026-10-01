import Mathlib
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»

/-!
# VF-mid as a fractional prime cluster on the integer square lattice

The continuous midpoint mass on the R-th square block is

  V_R = (2R+1) / log(R^2+R+1/2).

For arithmetic comparison the two square endpoints are composite, so the
physical prime carrier is the open integer block (R^2,(R+1)^2), which has
exactly 2R seats.  This file puts the complete VF mass uniformly on those
2R seats.  The resulting fractional-prime cluster has exactly mass V_R in
every block and exactly the cumulative VF-mid mass at square endpoints.

Thus VF-mid is literally an integer-lattice allocation of the already-proved
continuous midpoint quadrature.  No assertion about actual-prime tracking is
made by this construction; the signed difference from the 0/1 prime seats is
the direct VF discrepancy.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Uniform fractional prime mass carried by each physical integer seat in the
R-th open square block. -/
def vfMidFractionalPrimeSeatWeight (R : ℕ) : ℝ :=
  vfMidBandMass R / (2 * (R : ℝ))

/-- The actual 0/1 prime mass at one integer seat. -/
def vfMidActualPrimeSeatMass (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

/-- **Exact block allocation.**  Uniformly spreading the VF-mid mass over the
2R physical integer seats in the R-th open square block preserves the complete
midpoint mass exactly. -/
theorem vfMidFractionalPrimeSeatWeight_sum_squareBand
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ _n ∈ vfMidSquareBandSites R,
      vfMidFractionalPrimeSeatWeight R) =
      vfMidBandMass R := by
  rw [Finset.sum_const, nsmul_eq_mul, vfMidSquareBandSites_card]
  unfold vfMidFractionalPrimeSeatWeight
  push_cast
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  field_simp

/-- Summing the 0/1 seat masses is exactly the physical prime cardinality. -/
theorem vfMidActualPrimeSeatMass_sum_squareBand
    (R : ℕ) :
    (∑ n ∈ vfMidSquareBandSites R, vfMidActualPrimeSeatMass n) =
      ((vfMidSquareBandPrimes R).card : ℝ) := by
  unfold vfMidActualPrimeSeatMass vfMidSquareBandPrimes
  rw [← Finset.sum_filter]
  simp

/-- **Block discrepancy as integral-minus-fractional realization error.**
The direct VF band error is exactly the signed discrepancy between the actual
0/1 prime configuration and the indeterminate fractional VF cluster on the
same physical integer seats. -/
theorem vfMidSquareBandError_eq_fractionalPrimeClusterDiscrepancy
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareBandError R =
      ∑ n ∈ vfMidSquareBandSites R,
        (vfMidActualPrimeSeatMass n -
          vfMidFractionalPrimeSeatWeight R) := by
  unfold vfMidSquareBandError
  rw [Finset.sum_sub_distrib,
    vfMidActualPrimeSeatMass_sum_squareBand,
    vfMidFractionalPrimeSeatWeight_sum_squareBand R hR]

/-- Signed actual-minus-fractional VF discrepancy across a run of complete
square blocks.  This is the realization error of the 0/1 prime configuration
against the indeterminate VF cluster on exactly the same integer seats. -/
def vfMidFractionalPrimeClusterDiscrepancy (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    ∑ n ∈ vfMidSquareBandSites r,
      (vfMidActualPrimeSeatMass n -
        vfMidFractionalPrimeSeatWeight r)

/-- The cluster discrepancy is exactly the sum of the direct VF band errors. -/
theorem vfMidFractionalPrimeClusterDiscrepancy_eq_sum_bandError
    (A B : ℕ) (hA : 2 ≤ A) :
    vfMidFractionalPrimeClusterDiscrepancy A B =
      ∑ r ∈ Finset.Ico A B, vfMidSquareBandError r := by
  unfold vfMidFractionalPrimeClusterDiscrepancy
  apply Finset.sum_congr rfl
  intro r hr
  have hr2 : 2 ≤ r := hA.trans (Finset.mem_Ico.mp hr).1
  symm
  exact vfMidSquareBandError_eq_fractionalPrimeClusterDiscrepancy r hr2

/-- **Exact cumulative realization identity.**
Across any square-block run starting at A >= 2, the integral-minus-fractional
seat discrepancy telescopes to the square-endpoint VF error increment. -/
theorem vfMidFractionalPrimeClusterDiscrepancy_eq_endpointError_sub
    (A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidFractionalPrimeClusterDiscrepancy A B =
      vfMidSquareEndpointError B - vfMidSquareEndpointError A := by
  rw [vfMidFractionalPrimeClusterDiscrepancy_eq_sum_bandError A B hA]
  calc
    (∑ r ∈ Finset.Ico A B, vfMidSquareBandError r) =
        ∑ r ∈ Finset.Ico A B,
          (vfMidSquareEndpointError (r + 1) -
            vfMidSquareEndpointError r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr2 : 2 ≤ r := hA.trans (Finset.mem_Ico.mp hr).1
          have hstep := vfMidSquareEndpointError_succ r hr2
          linarith
    _ = vfMidSquareEndpointError B - vfMidSquareEndpointError A := by
          exact Finset.sum_Ico_sub vfMidSquareEndpointError hAB

/-- Cumulative fractional-prime mass through all complete square blocks below
the square endpoint R^2. -/
def vfMidFractionalPrimeClusterMass (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R,
    ∑ _n ∈ vfMidSquareBandSites r,
      vfMidFractionalPrimeSeatWeight r

/-- **The fractional cluster is exactly VF-mid at square endpoints.**
No approximation is involved in passing from the block midpoint masses to the
integer-lattice fractional allocation. -/
theorem vfMidFractionalPrimeClusterMass_eq_finishedMass
    (R : ℕ) :
    vfMidFractionalPrimeClusterMass R = vfMidFinishedMass R := by
  unfold vfMidFractionalPrimeClusterMass vfMidFinishedMass
  apply Finset.sum_congr rfl
  intro r hr
  have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
  exact vfMidFractionalPrimeSeatWeight_sum_squareBand r hr2

/-- At a square endpoint the integer-lattice fractional cluster is exactly the
real VF-mid path. -/
theorem vfMidFractionalPrimeClusterMass_eq_vfMid_sq
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidFractionalPrimeClusterMass R =
      vfMid ((R : ℝ) ^ 2) := by
  rw [vfMidFractionalPrimeClusterMass_eq_finishedMass,
    vfMid_sq hR]

/-- **Integer corollary of continuous Li.**
The exact integer-lattice fractional cluster differs from the repository's
continuous logarithmic integral by only root scale at every square endpoint.
This is an immediate corollary of the unconditional VF-mid midpoint
quadrature theorem. -/
theorem vfMidFractionalPrimeCluster_li_root_bounded :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ R : ℕ, 2 ≤ R →
        |vfMidFractionalPrimeClusterMass R -
          vfMidLogarithmicIntegralFromTwo ((R : ℝ) ^ 2)| ≤
            B * (R : ℝ) := by
  rcases vfMidLiRootBounded with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro R hR
  have h4nat : 4 ≤ R ^ 2 := by nlinarith
  have h4 : (4 : ℝ) ≤ (R : ℝ) ^ 2 := by exact_mod_cast h4nat
  have h := hB ((R : ℝ) ^ 2) h4
  have hRnonneg : 0 ≤ (R : ℝ) := by positivity
  rw [vfMidLiError,
    ← vfMidFractionalPrimeClusterMass_eq_vfMid_sq R hR,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hRnonneg] at h
  exact h

end RHLean.Analysis
