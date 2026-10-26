import OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval

/-!
# Original OpenAI low-Gaussian zero-frequency nonresonance

The original bareCongruenceCoefficient_unit_frequency proves exact
multiplicative covariance of the true finite-frequency coefficient.
At Fourier frequency 0, a nontrivial multiplicative phase forces the source
coefficient to vanish identically. This works for any coprime multiplier, not
only an Eisenstein unit. The calibrated result transports the vanishing
through the actual calibrationForSet factor, retaining the original ideals
and conductor exclusions.

The analytic nonzero-frequency power saving is not claimed here.
That requires the original radial Poisson tail and source admission.
-/

namespace OAI
noncomputable section

namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

/-- The original bare zero Fourier mode disappears as soon as any
coprime multiplier detects a nonprincipal residual character. -/
theorem bareCongruenceCoefficient_zero_mode_of_nontrivial
    (A s : O)
    (hA : Supported (Ideal.span {A}))
    (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b (A * s))
    (hphase :
      ((CanonicalRowCompletion.idealRowHom b (Ideal.span {A}))⁻¹ *
       CanonicalRowCompletion.idealRowHom b (Ideal.span {s})) ≠ 1) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) 0 = 0 := by
  let c : ℂ :=
    (CanonicalRowCompletion.idealRowHom b (Ideal.span {A}))⁻¹ *
    CanonicalRowCompletion.idealRowHom b (Ideal.span {s})
  let v : ℂ := bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) 0
  have heq : v = c * v := by
    simpa only [mul_zero] using
      (bareCongruenceCoefficient_unit_frequency A s hA hs b 0 hcop)
  have hp : (1 - c) * v = 0 := by
    calc
      (1 - c) * v = v - c * v := by ring
      _ = 0 := by rw [← heq]; ring
  have hc : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hphase)
  exact (mul_eq_zero.mp hp).resolve_left hc

/-- Actual original calibration: excluded-ideal and conductor factors are
retained. With true coprimality, vanishing transfers to the physical source. -/
theorem actualCongruenceCoefficient_zero_mode_of_nontrivial
    (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal)
    (A s : O)
    (hA : Supported (Ideal.span {A}))
    (hs : Supported (Ideal.span {s}))
    (hcal : IsCoprime (calibrationForSet S hS).generator (A * s))
    (b : O) (hcop : IsCoprime b (A * s))
    (hphase :
      ((CanonicalRowCompletion.idealRowHom b (Ideal.span {A}))⁻¹ *
       CanonicalRowCompletion.idealRowHom b (Ideal.span {s})) ≠ 1) :
    actualCongruenceCoefficient
      (calibrationForSet S hS) A s (supportedElement_ne_zero A hA) 0 = 0 := by
  have hbare :=
    bareCongruenceCoefficient_zero_mode_of_nontrivial
      A s hA hs b hcop hphase
  have htransport :=
    actualCongruenceCoefficient_calibration_factor
      S hS A s (supportedElement_ne_zero A hA) hs hcal 0
  dsimp only at htransport
  rw [hbare, mul_zero] at htransport
  exact htransport

#print axioms bareCongruenceCoefficient_zero_mode_of_nontrivial
#print axioms actualCongruenceCoefficient_zero_mode_of_nontrivial

end SevenEighths.ProbePhysical
end
end OAI
