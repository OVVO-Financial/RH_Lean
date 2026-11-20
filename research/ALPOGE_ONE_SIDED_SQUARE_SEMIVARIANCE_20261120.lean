import Mathlib
import RHLean.Analysis.NativePNTErrorMass
import RHLean.Proof.FinitePartialMoments

/-!
# One-sided square-prefix Chebyshev semivariance, in native NNS coordinates

This is the exact zero-target *lower* partial second moment of the genuine
von Mangoldt Chebyshev error at physical square endpoints R^2-1.

The proof target is a uniform dyadic bound of size H^(3+epsilon).
Classically, such a bound would imply RH via one-sided smoothing of
Alpoge's Gz and Landau's theorem; this file does NOT postulate or prove
that analytic implication, nor does it assume the unproved semivariance
bound. See research/ALPOGE_ONE_SIDED_SQUARE_SEMIVARIANCE_20261120.md.

We reuse FinitePartialMoments rather than introducing arbitrary
probabilistic independence of prime signs.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- The physical degree-two lower partial moment about zero on H<=R<2H,
using the complete native Chebyshev error psi(R^2-1)-(R^2-1). -/
def alpogeSquareNegativeSemivariance (H : ℕ) : ℝ :=
  lowerPartialMomentNat 2 (Finset.Ico H (2 * H))
    (fun R => nativePNTError (R ^ 2 - 1))

/-- Exact NNS LPM_2 interpretation, with no statistical assumptions and no
loss by bounding separate prime/cofactor pieces. -/
theorem alpogeSquareNegativeSemivariance_eq_explicit (H : ℕ) :
    alpogeSquareNegativeSemivariance H =
      ∑ R ∈ Finset.Ico H (2 * H),
        (max (((R ^ 2 - 1 : ℕ) : ℝ) - nativePsi (R ^ 2 - 1)) 0) ^ 2 := by
  unfold alpogeSquareNegativeSemivariance lowerPartialMomentNat
  apply Finset.sum_congr rfl
  intro R _hR
  simp only [negativePart, nativePNTError, neg_sub]

/-- A true semivariance is nonnegative at every finite cutoff. -/
theorem alpogeSquareNegativeSemivariance_nonneg (H : ℕ) :
    0 ≤ alpogeSquareNegativeSemivariance H := by
  unfold alpogeSquareNegativeSemivariance lowerPartialMomentNat
  exact Finset.sum_nonneg (fun R _hR =>
    sq_nonneg (negativePart (nativePNTError (R ^ 2 - 1))))

/-- The exact *unproved arithmetic supplier* needed for the one-sided
square-root Gz bound: dyadic lower partial energy of natural size H^3,
up to an arbitrarily small exponent loss.

The corresponding classical implication to RH is discussed in the
research note and requires an analytic tail bridge not claimed here. -/
def AlpogeCriticalSquareNegativeSemivariance : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ H : ℕ, 1 ≤ H →
        alpogeSquareNegativeSemivariance H ≤
          C * ((H : ℝ) ^ ((3 : ℝ) + epsilon))

end RHLean.Analysis
