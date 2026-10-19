import «research.VF_MID_919_DISCRETE_GAUSS_PARTIAL_MOMENT_COMPLETION_20261019»

/-!
# Exact Gauss magnitude on genuine split prime residue fields

No Lebesgue integration and no imported OpenAI results. For an actual
nonprincipal multiplicative character over the finite field ZMod p,
derive the flat Gauss size from two FINITE algebraic relations:
  star_gaussSum_eq
  gaussSum_mul_gaussSum_eq_card
and the native primitive additive character ZMod.stdAddChar.

This theorem proves ||τ||²=p. Parseval alone only bounds the AVERAGE
squared Fourier coefficient; multiplicativity, primitivity, and the
character twist are essential to individual flatness.

For ideals of composite norm D, a separate CRT and primitive-conductor
factorization is still necessary; imprimitive and ramified ideals must
retain the source's zero-extension branches.
-/

noncomputable section
namespace RHLean.Analysis

/-- Individual √p Gauss magnitude from exact finite field
    orthogonality, not from a continuous Fourier transform. -/
theorem vf919DiscreteSplitPrimeGauss_norm_sq
    {p : ℕ} (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (p : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hprod :
      gaussSum χ ZMod.stdAddChar *
          gaussSum χ⁻¹ ZMod.stdAddChar⁻¹ =
        (Fintype.card (ZMod p) : ℂ) :=
    gaussSum_mul_gaussSum_eq_card
      (χ := χ) (ψ := ZMod.stdAddChar)
      hχ (ZMod.isPrimitive_stdAddChar p)
  have hstar :
      gaussSum χ ZMod.stdAddChar *
          star (gaussSum χ ZMod.stdAddChar) = (p : ℂ) := by
    rw [star_gaussSum_eq χ ZMod.stdAddChar]
    simpa only [ZMod.card] using hprod
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hstar
  simpa [norm_mul, pow_two] using hnorm

#print axioms vf919DiscreteSplitPrimeGauss_norm_sq

end RHLean.Analysis
