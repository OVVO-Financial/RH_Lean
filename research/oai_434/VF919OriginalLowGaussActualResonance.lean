import OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval

/-!
# TRUE low Gaussian / actual rowTwist RESONANCE, with no stochastic assumptions

This is the exact physical obstruction to substituting a bare radial
nonprincipal sextic character estimate into OpenAI's compensated source.
The coefficient `rowTwist Psi b 1 m s` is the original inverse-theta
coefficient that actually appears inside correctedCompletedT. At the
squarefree column I=(s), it contains `idealRowHom m (s)`, the exact
inverse of `sexticGauss(s,-m)`'s oscillatory component.

For m coprime to s and b coprime to s the product is INDEPENDENT
of m. No Cauchy/triangle inequality, independence premise, or
favorable covariance is required for this conclusion.

This does NOT prove the global low signed saving. It proves that a
complete-row sextic phase cancellation cannot bound the
original FULL markedCompletedT without separately paying this
actual arithmetic resonant branch.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss

local notation "O" => ActualEisensteinCubic.O

/-- Real source resonance: Gaussian low sextic phase cancels the
  opposite true sextic phase inside the original inverse
  rowTwist coefficient at I=(s). A bare nonprincipal character
  bound cannot see or eliminate this term. -/
theorem actualLowGauss_inverseRowTwist_exact_resonance
    (s : O) (hs : Supported (Ideal.span {s}))
    (b m : O) (hb : IsCoprime b s)
    (hm : IsCoprime m s) (Psi : O →* ℂ) :
    sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      rowTwist Psi b 1 m s =
        sexticGauss s (supportedElement_ne_zero s hs) (-1) * Psi s := by
  have hchi : idealRowHom m (Ideal.span {s}) ≠ 0 :=
    idealRowHom_ne_zero_of_coprime s m hs hm.symm
  have h6 : idealRowHom (b^6) (Ideal.span {s}) = 1 := by
    rw [idealRowHom_sixth_mask b (Ideal.span {s}) hs]
    have hc : IsCoprime (Ideal.span {s}) (Ideal.span {b}) :=
      (Ideal.isCoprime_span_singleton_iff s b).mpr hb.symm
    simp [hc]
  have htwist :
      rowTwist Psi b 1 m s =
        Psi s * idealRowHom m (Ideal.span {s}) := by
    change Psi s * idealRowHom (b^6 * 1^4 * m) (Ideal.span {s}) = _
    simp only [one_pow, mul_one]
    rw [idealRowHom_argument_mul, h6, one_mul]
  have hgauss := sexticGauss_unit_scale s hs m (-1) hm
  rw [show m * (-1) = -m by ring] at hgauss
  rw [htwist, hgauss]
  calc
    (idealRowHom m (Ideal.span {s}))⁻¹ *
          sexticGauss s (supportedElement_ne_zero s hs) (-1) *
          (Psi s * idealRowHom m (Ideal.span {s})) =
        ((idealRowHom m (Ideal.span {s}))⁻¹ *
          idealRowHom m (Ideal.span {s})) *
          (sexticGauss s (supportedElement_ne_zero s hs) (-1) * Psi s) := by
      ring
    _ = _ := by rw [inv_mul_cancel₀ hchi, one_mul]

#print axioms actualLowGauss_inverseRowTwist_exact_resonance

end SevenEighths.ProbePhysical
end
end OAI
