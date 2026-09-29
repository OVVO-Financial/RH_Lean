import Mathlib
import «research.PRIME_FLIP_STATIC_CHRONOLOGY»
import «research.PRIME_FLIP_PNT_FINAL_STOKES_BRIDGE»

/-!
# Final conditional closure from a second-order PNT discrepancy hypothesis

This file does **not** claim that the classical prime number theorem proves RH.
The ordinary first-order statement `pi(x) ~ x/log x` is already a theorem and
is too weak to control the short reciprocal bands after their leading terms
cancel.

Instead, this module states the exact stronger prime-counting input exposed by
the chronology/PNT telescope: the Möbius-weighted `pi - Li` discrepancy must
have a signed energy effect no larger than the remaining quarter of the
compiled FinalStokes coefficient budget.

The deterministic Li model is kept as a separate model-side obligation.  Under

* model Stokes coefficient 2, and
* second-order signed PNT replacement coefficient 1/4,

the existing 9/4 FinalStokes consumer closes the Riemann hypothesis.

The point of the theorem is to make the conditional closure precise and
kernel-checked without relabeling an RH-strength or stronger statement as
ordinary PNT.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- The square-clock PNT replacement error written *only* in terms of the
classical prime-count discrepancy `Delta = pi - Li`, Möbius atoms, and the
single lower endpoint boundary.

This is the arbitrary-snapshot Abel telescope specialized to
`X = R^2 - 1`. -/
def squareRootSecondOrderPNTAtomError (R : ℕ) : ℂ :=
  -(∑ d ∈ Finset.Icc 2 (R - 1),
      (((μ d : ℤ) : ℂ)) *
        primeSievePrimeDiscrepancy (squareRootEndpoint R / d)) +
    (mertensSummatory (R - 1) - 1) * primeSievePrimeDiscrepancy R

/-- The atomized second-order prime-count error is exactly the previously
compiled prime-multiplicity replacement error. -/
theorem squareRootSecondOrderPNTAtomError_eq_primeFlipPNTError
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSecondOrderPNTAtomError R =
      primeFlipPNTError R (squareRootEndpoint R) := by
  unfold squareRootSecondOrderPNTAtomError
  symm
  exact squareRoot_primeFlipPNTError_eq_moebiusAtoms R hR

/-- Real scalar form used by the FinalStokes energy coordinates. -/
def squareRootSecondOrderPNTAtomErrorReal (R : ℕ) : ℝ :=
  (squareRootSecondOrderPNTAtomError R).re

theorem squareRootSecondOrderPNTAtomErrorReal_eq_replacementError
    (R : ℕ) (hR : 2 ≤ R) :
    squareRootSecondOrderPNTAtomErrorReal R =
      squareRootPrimeFlipPNTErrorReal R := by
  unfold squareRootSecondOrderPNTAtomErrorReal
    squareRootPrimeFlipPNTErrorReal primeFlipPNTErrorReal
  rw [squareRootSecondOrderPNTAtomError_eq_primeFlipPNTError R hR]

/-- **Second-order signed PNT hypothesis at the exact required scale.**

The input is explicitly a statement about the Möbius-weighted prime-counting
error exposed above.  It preserves the favorable `-4 e^2` term and therefore
does not replace the signed correction by an absolute-value estimate.

This is stronger than ordinary first-order PNT; the name records that fact. -/
def SquareRootSecondOrderPNTSignedReplacementBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    let e := squareRootSecondOrderPNTAtomErrorReal R
    4 * (lowOwnerPost789EndpointGapReal R +
          lowOwnerReciprocalMertensColumnReal R) * e -
        4 * e ^ 2 ≤
      (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R +
        C * (R : ℝ) ^ 2 * K

/-- The deterministic Li/PNT-density model side of the desired closure.  No
actual prime-count error appears here. -/
def SquareRootLiModelStokesBound (C : ℝ) : Prop :=
  LowOwnerPrimeFlipPNTModelStokesBound 2 C

/-- The explicit second-order PNT hypothesis is exactly strong enough to supply
the existing signed replacement-effect interface. -/
theorem primeFlipPNTReplacementEffectBound_of_secondOrderPNT
    {C : ℝ}
    (hPNT : SquareRootSecondOrderPNTSignedReplacementBound C) :
    LowOwnerPrimeFlipPNTReplacementEffectBound (1 / 4) C := by
  intro R K hR hK
  have h := hPNT R K hR hK
  rw [lowOwnerPrimeFlipPNTReplacementEffect_eq_actualCross_sub_errorSq]
  rw [← squareRootSecondOrderPNTAtomErrorReal_eq_replacementError R (by omega)]
  exact h

/-- **Conditional final proof.**

A root-scale bound for the deterministic Li model together with the exact
second-order Möbius-weighted prime-count discrepancy bound closes the existing
9/4 FinalStokes corridor and hence the Riemann hypothesis. -/
theorem riemannHypothesis_of_secondOrderPNT_and_liModel
    {Cm Ce : ℝ}
    (hCm : 0 ≤ Cm) (hCe : 0 ≤ Ce)
    (hModel : SquareRootLiModelStokesBound Cm)
    (hPNT : SquareRootSecondOrderPNTSignedReplacementBound Ce) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeFlipPNTModel_two_replacement_quarter
    hCm hCe hModel
      (primeFlipPNTReplacementEffectBound_of_secondOrderPNT hPNT)

/-- Existential package of the exact conditional route. -/
def SquareRootSecondOrderPNTClosureStatement : Prop :=
  ∃ Cm Ce : ℝ,
    0 ≤ Cm ∧
    0 ≤ Ce ∧
    SquareRootLiModelStokesBound Cm ∧
    SquareRootSecondOrderPNTSignedReplacementBound Ce

theorem riemannHypothesis_of_secondOrderPNTClosure
    (h : SquareRootSecondOrderPNTClosureStatement) :
    RiemannHypothesis := by
  rcases h with ⟨Cm, Ce, hCm, hCe, hModel, hPNT⟩
  exact riemannHypothesis_of_secondOrderPNT_and_liModel
    hCm hCe hModel hPNT

/-! ## Perfect multiplicity replacement diagnostic

Even the formally stronger idealization in which the prime-count replacement
error vanishes identically only removes the replacement-effect obligation.
The deterministic Li-model Stokes estimate remains.  This theorem prevents an
exact-density thought experiment from being mistaken for a proof of that
model-side bound.
-/

/-- Idealized zero-error prime multiplicity statement on every production
square clock.  This is **not** ordinary PNT and is not asserted to be true. -/
def SquareRootPerfectLiMultiplicityStatement : Prop :=
  ∀ R : ℕ, 56 ≤ R → squareRootSecondOrderPNTAtomErrorReal R = 0

theorem primeFlipPNTReplacementEffectBound_zero_of_perfectLiMultiplicity
    (hPerfect : SquareRootPerfectLiMultiplicityStatement) :
    LowOwnerPrimeFlipPNTReplacementEffectBound (1 / 4) 0 := by
  intro R K hR hK
  have he := hPerfect R hR
  rw [lowOwnerPrimeFlipPNTReplacementEffect_eq_actualCross_sub_errorSq,
    ← squareRootSecondOrderPNTAtomErrorReal_eq_replacementError R (by omega),
    he]
  have hE : 0 ≤ canonicalRoughLowQ2DaughterEnergy R :=
    canonicalRoughLowQ2DaughterEnergy_nonneg R
  have hquarter :
      0 ≤ (1 / 4 : ℝ) * canonicalRoughLowQ2DaughterEnergy R :=
    mul_nonneg (by norm_num) hE
  simpa using hquarter

/-- Under the idealized exact-Li multiplicity statement, the only remaining
condition is the deterministic Li-model Stokes bound. -/
theorem riemannHypothesis_of_perfectLiMultiplicity_and_liModel
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hPerfect : SquareRootPerfectLiMultiplicityStatement)
    (hModel : SquareRootLiModelStokesBound Cm) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primeFlipPNTModel_two_replacement_quarter
    hCm (by norm_num) hModel
      (primeFlipPNTReplacementEffectBound_zero_of_perfectLiMultiplicity hPerfect)

end RHLean.Analysis
