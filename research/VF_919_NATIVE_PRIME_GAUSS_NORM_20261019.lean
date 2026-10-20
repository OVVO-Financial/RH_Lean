import «research.VF_919_NATIVE_DISCRETE_GAUSS_PARTIAL_MOMENTS_20261019»

/-!
# Exact finite-field Gauss magnitude in RH_Lean's discrete character source

A native Mathlib/Finset proof of the magnitude of genuine Gauss sums
over a finite FIELD, using the two Gauss sums/conjugation identity and
the complete primitive additive-character orthogonality theorem.

This supplies a sqrt(card F) Gauss coefficient, WITHOUT importing any
OAI module, Lebesgue integration, or assuming a Gauss-envelope axiom.

For a composite Eisenstein ideal modulus the residue quotient need not
be a field. Extending this through ideal CRT and varying primitive
conductors is a separate mathematical requirement. Nor does this lemma
alone give the l1 Fourier-window saving or the final 7/8 theorem.
-/

noncomputable section

namespace RHLean.Analysis

/-- Over any finite field, a NONTRIVIAL multiplicative character
and a PRIMITIVE additive character have Gauss magnitude squared equal
to the number of field elements. Both hypotheses matter. -/
theorem vf919FiniteFieldGauss_squaredNorm
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have hmul := gaussSum_mul_gaussSum_eq_card hχ hψ
  -- Written before Mathlib exposed star_gaussSum_eq; kept unchanged.
  -- Prove the conjugation identity directly from the native
  -- multiplicative/additive character involutions.
  have hstar : star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
    calc
      _ = ∑ x : F, star (ψ x) * χ⁻¹ x := by
        simp [gaussSum, star_mul, MulChar.star_apply']
      _ = ∑ x : F, ψ⁻¹ x * χ⁻¹ x := by
        simp [← starRingEnd_apply, AddChar.map_neg_eq_conj]
      _ = _ := by simp [mul_comm, gaussSum]
  rw [← hstar] at hmul
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hmul
  simpa [norm_mul, pow_two] using hnorm

/-- At a genuine split rational prime p, each Eisenstein prime-ideal
residue field is F_p. Its nontrivial sextic character has exact Gauss
magnitude sqrt(p), independently of the rational norm projection. -/
theorem vf919SplitPrimeGauss_squaredNorm
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  have h := vf919FiniteFieldGauss_squaredNorm χ
    (ZMod.stdAddChar (N := p)) hχ
    (ZMod.isPrimitive_stdAddChar p)
  simpa using h

#print axioms vf919FiniteFieldGauss_squaredNorm
#print axioms vf919SplitPrimeGauss_squaredNorm

end RHLean.Analysis
