import «research.VF_919_ZERO_TARGET_DISCRETE_ABEL_GREEN_KUBO_20261020»
import «research.VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019»

/-!
# Instantiate the finite exterior Abel and NNS Gram theorems with ORIGINAL mu_Z

No free arithmetic label or model coefficient: f n is the established
original realMoebiusStep n at EVERY integer n, including squareful zeros.
The sharp base is X = K^2, and the exterior sites are exactly X < n < B
(for B = ceil((32/25)*X) in the final profile specialization).

This module makes no analytic claim: uniform covariance savings remain
open. All its arguments are finite sums; no Bochner integral appears.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Original integer square-boundary Mertens spill, expressed as the
    exact signed cumulative exterior mu_Z first partial moment. -/
theorem vf919OriginalSquareExteriorSpill_eq_discreteAbel
    (K B : ℕ) (hKB : K ^ 2 + 1 ≤ B)
    (H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo (K ^ 2) B, realMoebiusStep n * H n) =
      ∑ n ∈ Finset.Ioo (K ^ 2) B,
        vf919ExteriorSignedPrefix (K ^ 2) n realMoebiusStep *
          vf919ExteriorAbelWeight H n :=
  vf919ExteriorSpill_eq_discreteAbel (K ^ 2) B hKB realMoebiusStep H hB

/-- Exact NNS signed imbalance UPM-LPM for ORIGINAL physical mu_Z. -/
theorem vf919OriginalSquareExteriorSignedPartial_eq_upper_sub_lower
    (K n : ℕ) :
    vf919ExteriorSignedPrefix (K ^ 2) n realMoebiusStep =
      vf919ExteriorUpperPartial (K ^ 2) n realMoebiusStep -
        vf919ExteriorLowerPartial (K ^ 2) n realMoebiusStep :=
  vf919ExteriorSignedPrefix_eq_upper_sub_lower (K ^ 2) n realMoebiusStep

/-- The actual mu_Z exterior zero-target Green--Kubo covariance.
    The off-diagonal payment is signed, including all physical integer
    ordered pairs rather than a fabricated ideal/norm replacement. -/
theorem vf919OriginalSquareExteriorEnergy_eq_diagonal_add_covariance
    (K B : ℕ) (hKB : K ^ 2 + 1 ≤ B)
    (H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo (K ^ 2) B,
      vf919ExteriorAbelWeight H n *
        (vf919ExteriorSignedPrefix (K ^ 2) n realMoebiusStep) ^ 2) =
      vf919ExteriorDiagonal (K ^ 2) B realMoebiusStep H +
        2 * vf919ExteriorPositiveLag (K ^ 2) B realMoebiusStep H :=
  vf919ExteriorAbelEnergy_eq_diagonal_add_covariance
    (K ^ 2) B hKB realMoebiusStep H hB

/-- Weighted original signed source: the only hypotheses are explicit
    nonnegative increments and total mass at most one. No moment bound
    is hidden in these finite arithmetic statements. -/
theorem vf919OriginalSquareExteriorSpill_sq_le_signedCovariance
    (K B : ℕ) (hKB : K ^ 2 + 1 ≤ B)
    (H : ℕ → ℝ) (hB : H B = 0)
    (hNu : ∀ n ∈ Finset.Ioo (K ^ 2) B,
      0 ≤ vf919ExteriorAbelWeight H n)
    (hMass : H (K ^ 2 + 1) ≤ 1) :
    (∑ n ∈ Finset.Ioo (K ^ 2) B, realMoebiusStep n * H n) ^ 2 ≤
      vf919ExteriorDiagonal (K ^ 2) B realMoebiusStep H +
        2 * vf919ExteriorPositiveLag (K ^ 2) B realMoebiusStep H := by
  exact (vf919ExteriorSpill_sq_le_AbelEnergy
      (K ^ 2) B hKB realMoebiusStep H hB hNu hMass).trans_eq
    (vf919OriginalSquareExteriorEnergy_eq_diagonal_add_covariance K B hKB H hB)

/-- Physical mu_Z UPM^2+LPM^2-2 UPM*LPM is exactly K+2 C. -/
theorem vf919OriginalSquareExteriorUpperLowerEnergy_eq_signedCovariance
    (K B : ℕ) (hKB : K ^ 2 + 1 ≤ B)
    (H : ℕ → ℝ) (hB : H B = 0) :
    (∑ n ∈ Finset.Ioo (K ^ 2) B,
      vf919ExteriorAbelWeight H n *
        ((vf919ExteriorUpperPartial (K ^ 2) n realMoebiusStep) ^ 2 +
         (vf919ExteriorLowerPartial (K ^ 2) n realMoebiusStep) ^ 2 -
         2 * vf919ExteriorUpperPartial (K ^ 2) n realMoebiusStep *
           vf919ExteriorLowerPartial (K ^ 2) n realMoebiusStep)) =
      vf919ExteriorDiagonal (K ^ 2) B realMoebiusStep H +
        2 * vf919ExteriorPositiveLag (K ^ 2) B realMoebiusStep H :=
  vf919ExteriorUpperLowerEnergy_eq_signedCovariance
    (K ^ 2) B hKB realMoebiusStep H hB

#print axioms vf919OriginalSquareExteriorSpill_eq_discreteAbel
#print axioms vf919OriginalSquareExteriorSignedPartial_eq_upper_sub_lower
#print axioms vf919OriginalSquareExteriorEnergy_eq_diagonal_add_covariance
#print axioms vf919OriginalSquareExteriorSpill_sq_le_signedCovariance
#print axioms vf919OriginalSquareExteriorUpperLowerEnergy_eq_signedCovariance

end RHLean.Analysis
