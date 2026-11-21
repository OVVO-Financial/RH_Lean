import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Analysis.AlpogeNNSBandSchur

/-!
# Source-exact matched Selberg: kill the artificial quadratic prime principal mode

The precise original signed second-Selberg recurrence contains the term
  (K2*E)(N) - (Lambda*S)(N).
The latter must be expanded by the PREEXISTING
  nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution
before any positive/negative partial moment is estimated.

Doing so matches K2 against Lambda*Lambda on the SAME physical
product, with no omitted prime square and no unowned semiprime.
At every n, K2(n)-(Lambda*Lambda)(n)=-Lambda(n)*log(n).
Therefore ALL distinct-prime semiprime responses cancel
term-for-term and only genuine prime powers remain in this matched
channel. The apparent large negative rank-one Schur principal mode
of a selected quadratic prime band is cancelled by its matching
convolution. This is a real source-preserving simplification, NOT a
power saving on the remaining complete prime-power renewal.

The exact full remaining source is still the Chebyshev error times
log(N)^2. We do not claim a uniform RH-strength bound on it.
-/

noncomputable section
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- A literal fully matched K2-Lambda*Lambda coefficient on the ORIGINAL
integer source. No character or statistical surrogate is inserted. -/
def alpogeNNSMatchedKernel (n : ℕ) : ℝ :=
  nativePNTSignedSecondSelbergKernel n - (Λ * Λ) n

/-- The second prime-pair polynomial disappears COMPLETELY after its
ordered convolution is restored. The only surviving coefficient is
first-order, on genuine von Mangoldt prime powers. -/
theorem alpogeNNSMatchedKernel_eq_negativePrimePower
    (n : ℕ) :
    alpogeNNSMatchedKernel n = -(Λ n * Real.log (n : ℝ)) := by
  unfold alpogeNNSMatchedKernel nativePNTSignedSecondSelbergKernel
  ring

/-- Every distinct prime-pair contribution to the matched source is ZERO,
even at an arbitrary reciprocal quotient, including endpoint 1. -/
theorem alpogeNNSMatchedKernel_distinctPrimes_zero
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    alpogeNNSMatchedKernel (p * q) = 0 := by
  have h := nativePNTSignedSecondSelbergKernel_eq_lambdaTwo_sub_two_log (p * q)
  rw [nativePNTSignedSecondSelbergKernel_mul_distinct_primes p q hp hq hne,
      nativeLambdaTwo_mul_distinct_primes p q hp hq hne] at h
  unfold alpogeNNSMatchedKernel nativePNTSignedSecondSelbergKernel
  linarith only [h]

/-- Any retained physical site mask, including all prime powers,
inherits the full signed prime-power match. -/
def alpogeNNSMatchedMass (N : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, alpogeNNSMatchedKernel n * nativePNTError (N / n)

/-- One scalar signed prime-power source, never a separately estimated
K2 plus convolution. -/
theorem alpogeNNSMatchedMass_eq_negativePrimePower
    (N : ℕ) (A : Finset ℕ) :
    alpogeNNSMatchedMass N A =
      -(∑ n ∈ A, Λ n * Real.log (n : ℝ) * nativePNTError (N / n)) := by
  unfold alpogeNNSMatchedMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [alpogeNNSMatchedKernel_eq_negativePrimePower]
  ring

/-- The complete signed Selberg second kernel after it has been matched
with the entire ordered Lambda-Lambda cofactor response. -/
theorem alpogeNNSMatchedMass_full_eq_K2_sub_convolution
    (N : ℕ) :
    alpogeNNSMatchedMass N (Finset.Icc 1 N) =
      nativePNTSignedSecondSelbergKernelErrorMass N -
      nativePNTLambdaConvolutionSignedErrorMass N := by
  unfold alpogeNNSMatchedMass alpogeNNSMatchedKernel
    nativePNTSignedSecondSelbergKernelErrorMass
    nativePNTLambdaConvolutionSignedErrorMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- THE COMPLETE source-level cancellation. This is the original E(N),
not a K2-only sector. ALL physical prime powers, both signed lower
remainders and the original floor defect remain. -/
theorem alpogeNNSNativeError_eq_matched_primePowerSource
    (N : ℕ) :
    nativePNTError N * (Real.log (N : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
      nativePNTLambdaFloorLogSignedErrorMass N -
      nativePNTLambdaFloorLogSignedDefectMass N +
      alpogeNNSMatchedMass N (Finset.Icc 1 N) := by
  have hselberg := nativePNTError_mul_log_sq_eq_signedSecondSelberg N
  have hfloor := nativePNTLambdaFloorLogSignedErrorMass_eq_remainder_sub_convolution N
  have hmatch := alpogeNNSMatchedMass_full_eq_K2_sub_convolution N
  linarith [hselberg, hfloor, hmatch]

/-- A physical mask A on actual integer products and its full complement
partition the complete original source without reintroducing the
quadratic prime principal mode. -/
theorem alpogeNNSNativeError_eq_matched_mask_and_rest
    (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    nativePNTError N * (Real.log (N : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder N * Real.log (N : ℝ) -
      nativePNTLambdaFloorLogSignedErrorMass N -
      nativePNTLambdaFloorLogSignedDefectMass N +
      alpogeNNSMatchedMass N ((Finset.Icc 1 N) \ A) +
      alpogeNNSMatchedMass N A := by
  have hpartition :
      alpogeNNSMatchedMass N ((Finset.Icc 1 N) \ A) +
      alpogeNNSMatchedMass N A =
        alpogeNNSMatchedMass N (Finset.Icc 1 N) := by
    unfold alpogeNNSMatchedMass
    exact Finset.sum_sdiff hA
  have hfull := alpogeNNSNativeError_eq_matched_primePowerSource N
  linarith [hpartition, hfull]

/-- The exact NNS signed quadratic band and the original ordered
Lambda-Lambda quadratic band have IDENTICAL principal rank-one modes.
After complete source matching, this mode cancels, leaving ONLY the
positive prime-square diagonal, not a large negative credit.

The physical instance of the identity is already proved in
research/SELBERG_MATCHED_PRODUCT_FACE.lean, theorem
selbergMatched_schur, with genuine p_i and literal quotient 1. -/
def alpogeNNSBandOrderedConvolutionCharge
    (m : ℕ) (ell : Fin m → ℝ) : ℝ :=
  -(∑ i : Fin m, ell i) ^ 2

theorem alpogeNNSBand_principalMode_cancels
    (m : ℕ) (ell : Fin m → ℝ) :
    alpogeNNSBandCharge m ell -
      alpogeNNSBandOrderedConvolutionCharge m ell =
        2 * ∑ i : Fin m, (ell i) ^ 2 := by
  unfold alpogeNNSBandCharge
    alpogeNNSBandOrderedConvolutionCharge
  ring

/-- The apparent strongly negative principal-mode saving disappears
when the full ordered convolution is restored. In Schur language the
matched source is exactly the DIAGONAL with no principal-mode tax. -/
theorem alpogeNNSBand_matchedScaledSchur_identity
    (m : ℕ) (ell : Fin m → ℝ) :
    (m : ℝ) * (alpogeNNSBandCharge m ell -
      alpogeNNSBandOrderedConvolutionCharge m ell) =
        2 * alpogeNNSBandScaledSchur m ell +
          2 * (∑ i : Fin m, ell i) ^ 2 := by
  rw [alpogeNNSBand_principalMode_cancels]
  unfold alpogeNNSBandScaledSchur
  ring

end RHLean.Analysis
