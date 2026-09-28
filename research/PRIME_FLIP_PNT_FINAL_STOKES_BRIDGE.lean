import Mathlib
import «research.PRIME_FLIP_PNT_TELESCOPE»
import «research.GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE»

/-!
# Prime-flip PNT multiplicity replacement wired to FinalStokes

The lightweight telescope module first performs the exact Euler/sign-flip
cancellation, groups identical inherited responses, and replaces only the prime
multiplicity by the repository's Li/PNT density.  This module attaches that
signed replacement error to the current post-789 FinalStokes amplitude.

No arithmetic upper bound is inserted here.  The point is to make the two
remaining quantitative obligations literal inputs to the existing 9/4
FinalStokes consumer.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Prime-location replacement error on the production square clock. -/
def squareRootPrimeFlipPNTErrorReal (R : ℕ) : ℝ :=
  primeFlipPNTErrorReal R (squareRootEndpoint R)

/-- The post-789 global amplitude with only the late-prime multiplicities
replaced by the Li/PNT model.  The actual lower Möbius responses are unchanged. -/
def lowOwnerPrimeFlipPNTModelAmplitude (R : ℕ) : ℝ :=
  lowOwnerPost789EndpointGapReal R +
    lowOwnerReciprocalMertensColumnReal R -
      2 * squareRootPrimeFlipPNTErrorReal R

/-- Final-Stokes energy of the multiplicity-replaced model. -/
def lowOwnerPrimeFlipPNTModelStokes (R : ℕ) : ℝ :=
  lowOwnerPrimeFlipPNTModelAmplitude R ^ 2 -
    lowOwnerZeroFrequencyMobiusDiagonal R

/-- Exact signed cost of returning from Li/PNT multiplicities to the actual
prime multiplicities inside the assembled post-789 amplitude. -/
def lowOwnerPrimeFlipPNTReplacementEffect (R : ℕ) : ℝ :=
  let e := squareRootPrimeFlipPNTErrorReal R
  4 * lowOwnerPrimeFlipPNTModelAmplitude R * e + 4 * e ^ 2

/-- The same replacement effect in actual-amplitude coordinates.  This is the
form that retains the favorable negative error square:
`4 A e - 4 e^2 = 4 e (A-e)`, where `A=G+Q`. -/
theorem lowOwnerPrimeFlipPNTReplacementEffect_eq_actualCross_sub_errorSq
    (R : ℕ) :
    lowOwnerPrimeFlipPNTReplacementEffect R =
      4 * (lowOwnerPost789EndpointGapReal R +
          lowOwnerReciprocalMertensColumnReal R) *
          squareRootPrimeFlipPNTErrorReal R -
        4 * squareRootPrimeFlipPNTErrorReal R ^ 2 := by
  unfold lowOwnerPrimeFlipPNTReplacementEffect
    lowOwnerPrimeFlipPNTModelAmplitude
  dsimp
  ring

/-- Factored version of the same signed replacement term. -/
theorem lowOwnerPrimeFlipPNTReplacementEffect_eq_four_error_mul_actual_sub_error
    (R : ℕ) :
    lowOwnerPrimeFlipPNTReplacementEffect R =
      4 * squareRootPrimeFlipPNTErrorReal R *
        ((lowOwnerPost789EndpointGapReal R +
            lowOwnerReciprocalMertensColumnReal R) -
          squareRootPrimeFlipPNTErrorReal R) := by
  rw [lowOwnerPrimeFlipPNTReplacementEffect_eq_actualCross_sub_errorSq]
  ring

/-- **Production energy split.**  The current final-Stokes object is exactly
the PNT-multiplicity model plus the signed replacement effect.  No norm is
taken on the two pieces separately. -/
theorem lowOwnerFinalStokes_eq_primeFlipPNTModel_add_replacement
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerCanonicalSignedStokesFinalBoundary R =
      lowOwnerPrimeFlipPNTModelStokes R +
        lowOwnerPrimeFlipPNTReplacementEffect R := by
  rw [lowOwnerCanonicalSignedStokesFinalBoundary_eq_post789GlobalAmplitudeSq_sub_diagonal hR]
  unfold lowOwnerPrimeFlipPNTModelStokes lowOwnerPrimeFlipPNTReplacementEffect
    lowOwnerPrimeFlipPNTModelAmplitude squareRootPrimeFlipPNTErrorReal
  dsimp
  ring

/-- Uniform model-side FinalStokes estimate, stated in the existing q²
recursive currency. -/
def LowOwnerPrimeFlipPNTModelStokesBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerPrimeFlipPNTModelStokes R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- Uniform signed replacement-effect estimate.  This is deliberately not an
absolute-value bound: favorable actual-vs-PNT covariance remains available. -/
def LowOwnerPrimeFlipPNTReplacementEffectBound (B C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerPrimeFlipPNTReplacementEffect R ≤
      B * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- The two new obligations add directly to an ordinary final-Stokes bound. -/
theorem finalStokesQ2EnergyBound_of_primeFlipPNTSplit
    {Bm Be Cm Ce : ℝ}
    (hModel : LowOwnerPrimeFlipPNTModelStokesBound Bm Cm)
    (hEffect : LowOwnerPrimeFlipPNTReplacementEffectBound Be Ce) :
    LowOwnerFinalStokesQ2EnergyBound (Bm + Be) (Cm + Ce) := by
  intro R K hR hK
  have hm := hModel R K hR hK
  have he := hEffect R K hR hK
  rw [lowOwnerFinalStokes_eq_primeFlipPNTModel_add_replacement hR]
  linarith

/-- Concrete coefficient allocation for the current consumer: coefficient 2
for the density-model Stokes term and only 1/4 for the signed replacement. -/
theorem finalStokesQ2EnergyBound_nineQuarters_of_primeFlipPNTSplit
    {Cm Ce : ℝ}
    (hModel : LowOwnerPrimeFlipPNTModelStokesBound 2 Cm)
    (hEffect : LowOwnerPrimeFlipPNTReplacementEffectBound (1 / 4) Ce) :
    LowOwnerFinalStokesQ2EnergyBound (9 / 4) (Cm + Ce) := by
  have h := finalStokesQ2EnergyBound_of_primeFlipPNTSplit hModel hEffect
  convert h using 1 <;> norm_num

/-- Direct conditional RH closure for the four-step prime-flip/PNT route.  The
two displayed quantitative hypotheses are exactly what remains to be proved in
these coordinates. -/
theorem riemannHypothesis_of_primeFlipPNTModel_two_replacement_quarter
    {Cm Ce : ℝ} (hCm : 0 ≤ Cm) (hCe : 0 ≤ Ce)
    (hModel : LowOwnerPrimeFlipPNTModelStokesBound 2 Cm)
    (hEffect : LowOwnerPrimeFlipPNTReplacementEffectBound (1 / 4) Ce) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_finalStokesQ2EnergyBound_nineQuarters
    (C := Cm + Ce) (by linarith)
  exact finalStokesQ2EnergyBound_nineQuarters_of_primeFlipPNTSplit hModel hEffect

end RHLean.Analysis
