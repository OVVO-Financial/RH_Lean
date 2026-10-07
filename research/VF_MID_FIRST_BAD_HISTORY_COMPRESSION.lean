import Mathlib
import «research.VF_MID_NATIVE_LYAPUNOV_SEAT_GRAM»
import «research.VF_MID_ACTUAL_PRIME_FIRST_BAD_MOBIUS_TRIGGER»
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import «research.VF_MID_FIRST_BAD_TERMINAL_CONTRADICTION»

/-!
# First-bad historical-anchor decompression

The one-block NNS formulation compresses all prior VF history into the scalar
endpoint defect D_R.  That compression is exact at the signed-mass level but
not neutral for the NNS denominator, because absolute value is nonlinear.

This file records the exact historical decomposition that any valid #900
owner-tree argument must use.  No packet-to-full-scale inheritance is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Exact historical decompression of the actual VF endpoint defect. -/
theorem vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    vfMidActualPrimeEndpointDefect R =
      vfMidActualPrimeEndpointDefect A - vfMidOddRunSeatMass A R := by
  unfold vfMidActualPrimeEndpointDefect
  rw [← vfMidDirectSquareEndpointError_eq_vfMidPrimeError
      (R := R) (hA.trans hAR),
    ← vfMidDirectSquareEndpointError_eq_vfMidPrimeError
      (R := A) hA]
  change
    vfMidSquareEndpointError R =
      vfMidSquareEndpointError A - vfMidOddRunSeatMass A R
  have hrun :=
    vfMidOddRunSeatMass_eq_neg_endpointError_increment A R hA hAR
  linarith

/-- The decompressed historical run is literally the finite sum of physical
odd-seat charges over all prior square blocks. -/
theorem vfMidOddRunSeatMass_eq_sum_physicalSeats
    (A R : ℕ) :
    vfMidOddRunSeatMass A R =
      ∑ r ∈ Finset.Ico A R,
        ∑ n ∈ vfMidOddCandidateSeats r,
          vfMidOddSignedSeatCharge r n := by
  rfl

/-- Compression can only reduce the historical absolute mass.  This is the
precise denominator issue: replacing the scalar D_R by its historical seats
does not preserve the NNS denominator. -/
theorem abs_vfMidActualPrimeEndpointDefect_le_anchor_add_historyAbs
    {A R : ℕ} (hA : 2 ≤ A) (hAR : A ≤ R) :
    |vfMidActualPrimeEndpointDefect R| ≤
      |vfMidActualPrimeEndpointDefect A| +
        ∑ r ∈ Finset.Ico A R,
          ∑ n ∈ vfMidOddCandidateSeats r,
            |vfMidOddSignedSeatCharge r n| := by
  rw [vfMidActualPrimeEndpointDefect_eq_anchor_sub_oddRunSeatMass hA hAR]
  calc
    |vfMidActualPrimeEndpointDefect A - vfMidOddRunSeatMass A R| ≤
        |vfMidActualPrimeEndpointDefect A| +
          |vfMidOddRunSeatMass A R| := abs_sub _ _
    _ ≤
        |vfMidActualPrimeEndpointDefect A| +
          ∑ r ∈ Finset.Ico A R,
            ∑ n ∈ vfMidOddCandidateSeats r,
              |vfMidOddSignedSeatCharge r n| := by
      gcongr
      unfold vfMidOddRunSeatMass vfMidOddBlockSeatMass
      calc
        |∑ r ∈ Finset.Ico A R,
            ∑ n ∈ vfMidOddCandidateSeats r,
              vfMidOddSignedSeatCharge r n| ≤
          ∑ r ∈ Finset.Ico A R,
            |∑ n ∈ vfMidOddCandidateSeats r,
              vfMidOddSignedSeatCharge r n| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤
          ∑ r ∈ Finset.Ico A R,
            ∑ n ∈ vfMidOddCandidateSeats r,
              |vfMidOddSignedSeatCharge r n| := by
            apply Finset.sum_le_sum
            intro r _hr
            exact Finset.abs_sum_le_sum_abs _ _

/-- At a hypothetical first bad successor every prior historical anchor remains
inside the same K=2 radial wall.  This is where first-badness must enter any
history-compression estimate. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_priorAnchor_inside
    {R A : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hA : 2 ≤ A) (hAR : A ≤ R) :
    |vfMidActualPrimeEndpointDefect A| ≤
      2 * vfMidSyntheticRadialScale A := by
  exact vfMidActualPrimeFirstBadAt_prior_inside
    hfirst hA (by omega : A < R + 1)

/-- The sharpened midpoint quadrature theorem used by the direct VF route:
at square endpoints VF_mid and Li differ by one fixed constant, not merely
root scale. -/
theorem vfMidLi_squareEndpoint_O_one
    {R : ℕ} (hR : 2 ≤ R) :
    |vfMidLiError ((R : ℝ) ^ 2)| ≤
      vfMidLiSquareEndpointUniformConstant :=
  abs_vfMidLiError_sq_le_uniform hR



/-- **Square-endpoint actual-prime/VF defect is a bounded perturbation of the
classical prime-minus-Li discrepancy.**

This is the exact sign convention used by the direct VF route:
`prime-Li = prime-VF + (VF-Li)`. -/
theorem vfMidActualPrimeEndpointDefect_eq_primeLi_sub_liError
    {R : ℕ} (hR : 2 ≤ R) :
    vfMidActualPrimeEndpointDefect R =
      vfMidPrimeLiError ((R : ℝ) ^ 2) -
        vfMidLiError ((R : ℝ) ^ 2) := by
  have hD :=
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := R) hR
  have hprime :=
    vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR
  have hsplit :=
    vfMidPrimeLiError_eq_primeError_add_liError ((R : ℝ) ^ 2)
  rw [hD]
  change vfMidDirectSquareEndpointError R = _
  rw [hprime]
  linarith

/-- Consequently the VF endpoint defect and the classical prime-minus-Li
discrepancy differ by the same fixed square-endpoint quadrature constant. -/
theorem abs_vfMidActualPrimeEndpointDefect_sub_primeLi_le_uniform
    {R : ℕ} (hR : 2 ≤ R) :
    |vfMidActualPrimeEndpointDefect R -
        vfMidPrimeLiError ((R : ℝ) ^ 2)| ≤
      vfMidLiSquareEndpointUniformConstant := by
  rw [vfMidActualPrimeEndpointDefect_eq_primeLi_sub_liError hR]
  have hquad := abs_vfMidLiError_sq_le_uniform (R := R) hR
  simpa [sub_sub, abs_neg] using hquad

end RHLean.Analysis
