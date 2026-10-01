import Mathlib
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»
import «research.VF_MID_DYADIC_SUMMATION_TRANSFER»

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

/-- The cumulative fractional-cluster discrepancy is exactly the existing
square-endpoint prime-minus-VF increment. -/
theorem vfMidFractionalPrimeClusterDiscrepancy_eq_primeError_increment
    {A B : ℕ} (hA : 2 ≤ A) (hB : 2 ≤ B) (hAB : A ≤ B) :
    vfMidFractionalPrimeClusterDiscrepancy A B =
      vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2) := by
  rw [vfMidFractionalPrimeClusterDiscrepancy_eq_endpointError_sub
    A B hA hAB]
  change
    vfMidDirectSquareEndpointError B -
        vfMidDirectSquareEndpointError A =
      vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2)
  rw [vfMidDirectSquareEndpointError_eq_vfMidPrimeError hB,
    vfMidDirectSquareEndpointError_eq_vfMidPrimeError hA]

/-- The sole dyadic arithmetic statement for the fractional-cluster route. -/
def VFMidFractionalPrimeClusterDyadicBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ A B : ℕ, 2 ≤ A → A < B → B ≤ 2 * A →
      |vfMidFractionalPrimeClusterDiscrepancy A B| ≤
        C * (A : ℝ) * Real.log A

/-- A root-log discrepancy bound for the 0/1 realization of the VF cluster
supplies the existing local dyadic increment consumer directly. -/
theorem vfMidDyadicIncrementBounded_of_fractionalPrimeCluster
    (hcluster : VFMidFractionalPrimeClusterDyadicBoundedStatement) :
    VFMidDyadicIncrementBoundedStatement := by
  rcases hcluster with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  intro A B hA hAB hBA
  have hB2 : 2 ≤ B := hA.trans hAB.le
  have hbound := hC A B hA hAB hBA
  rw [vfMidFractionalPrimeClusterDiscrepancy_eq_primeError_increment
    hA hB2 hAB.le] at hbound
  have hfour : 0 ≤ 4 * (A : ℝ) := by positivity
  linarith

/-- Conversely, the square-endpoint von-Koch bound controls every dyadic
fractional-cluster realization increment.  Thus the cluster formulation loses
no arithmetic information. -/
theorem vfMidFractionalPrimeClusterDyadicBounded_of_squareEndpoint
    (hsq : VFMidSquareEndpointVonKochBoundedStatement) :
    VFMidFractionalPrimeClusterDyadicBoundedStatement := by
  rcases hsq with ⟨K, hK0, hK⟩
  refine ⟨5 * K, mul_nonneg (by norm_num) hK0, ?_⟩
  intro A B hA hAB hBA
  have hB2 : 2 ≤ B := hA.trans hAB.le
  rw [vfMidFractionalPrimeClusterDiscrepancy_eq_primeError_increment
    hA hB2 hAB.le]
  have hEA := hK A hA
  have hEB := hK B hB2
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogA0 : 0 ≤ Real.log (A : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ A by omega))
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hBAreal : (B : ℝ) ≤ 2 * (A : ℝ) := by
    exact_mod_cast hBA
  have hlogB_le_log2A :
      Real.log (B : ℝ) ≤ Real.log (2 * (A : ℝ)) :=
    Real.log_le_log hBpos hBAreal
  have hlog2A :
      Real.log (2 * (A : ℝ)) =
        Real.log 2 + Real.log (A : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hApos.ne']
  have hlog2_le_logA :
      Real.log 2 ≤ Real.log (A : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hA)
  have hlogB_le_two_logA :
      Real.log (B : ℝ) ≤ 2 * Real.log (A : ℝ) := by
    rw [hlog2A] at hlogB_le_log2A
    linarith
  have hBscale :
      (B : ℝ) * Real.log (B : ℝ) ≤
        4 * (A : ℝ) * Real.log (A : ℝ) := by
    calc
      (B : ℝ) * Real.log (B : ℝ) ≤
          (2 * (A : ℝ)) * Real.log (B : ℝ) :=
        mul_le_mul_of_nonneg_right hBAreal hlogB0
      _ ≤ (2 * (A : ℝ)) * (2 * Real.log (A : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogB_le_two_logA (by positivity)
      _ = 4 * (A : ℝ) * Real.log (A : ℝ) := by ring
  have hKBscale :
      K * (B : ℝ) * Real.log (B : ℝ) ≤
        4 * K * (A : ℝ) * Real.log (A : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hBscale hK0
    nlinarith
  calc
    |vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2)|
        ≤ |vfMidPrimeError ((B : ℝ) ^ 2)| +
            |vfMidPrimeError ((A : ℝ) ^ 2)| := abs_sub _ _
    _ ≤ K * (B : ℝ) * Real.log B +
          K * (A : ℝ) * Real.log A :=
      add_le_add hEB hEA
    _ ≤ 5 * K * (A : ℝ) * Real.log A := by
      nlinarith [hKBscale]

/-- **Fractional-cluster square-endpoint closure.**
Once the integral 0/1 prime realization tracks the VF fractional cluster on
every dyadic square run, the full VF square-endpoint von-Koch estimate follows
from the already-compiled dyadic summation theorem. -/
theorem vfMidSquareEndpointVonKochBounded_of_fractionalPrimeCluster
    (hcluster : VFMidFractionalPrimeClusterDyadicBoundedStatement) :
    VFMidSquareEndpointVonKochBoundedStatement :=
  vfMidSquareEndpointVonKochBounded_of_dyadicIncrement
    (vfMidDyadicIncrementBounded_of_fractionalPrimeCluster hcluster)

/-- **Exact arithmetic equivalence.**
The dyadic 0/1-versus-fractional VF realization bound is equivalent to the
official square-endpoint von-Koch target. -/
theorem vfMidFractionalPrimeClusterDyadicBounded_iff_squareEndpoint :
    VFMidFractionalPrimeClusterDyadicBoundedStatement ↔
      VFMidSquareEndpointVonKochBoundedStatement := by
  constructor
  · exact vfMidSquareEndpointVonKochBounded_of_fractionalPrimeCluster
  · exact vfMidFractionalPrimeClusterDyadicBounded_of_squareEndpoint

/-- With the standard classical von-Koch criterion supplied, the VF
fractional-cluster realization statement is exactly equivalent to RH. -/
theorem vfMidFractionalPrimeClusterDyadicBounded_iff_riemannHypothesis
    (criterion : ClassicalVonKochRHCriterion) :
    VFMidFractionalPrimeClusterDyadicBoundedStatement ↔
      VFMidRiemannHypothesisStatement := by
  rw [vfMidFractionalPrimeClusterDyadicBounded_iff_squareEndpoint,
    vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded,
    criterion.iff_riemannHypothesis]

/-- **End-to-end VF fractional-cluster consumer.**
The continuous Li -> VF quadrature error is discharged unconditionally by the
existing midpoint theorem.  The only arithmetic input here is the dyadic
integral-realization discrepancy of actual primes against the VF cluster. -/
theorem riemannHypothesis_of_vfMidFractionalPrimeCluster
    (criterion : ClassicalVonKochRHCriterion)
    (hcluster : VFMidFractionalPrimeClusterDyadicBoundedStatement) :
    VFMidRiemannHypothesisStatement :=
  riemannHypothesis_of_vfMidSquareEndpoint criterion
    (vfMidSquareEndpointVonKochBounded_of_fractionalPrimeCluster hcluster)

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
