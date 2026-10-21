import «research.VF_919_NATIVE_PRIME_GAUSS_NORM_20261019»

/-!
# Exact Gauss magnitude on genuine split prime residue fields

Import only the native finite-field norm dependency. The independently
compiled finite-character completion module also declares discrete UPM/LPM
helpers under the same namespace and must not be joined through an
unnecessary import diamond.

No Lebesgue integration or OpenAI proof import. Reuse the native
finite-field conjugation and Gauss-product theorem already verified
under the pinned toolchain; it does not depend on Mathlib's
star_gaussSum_eq.

The modulus has an explicit NeZero instance, as required to construct
ZMod p's finite residue field before elaborating the theorem statement.
Primality remains an explicit mathematical hypothesis.

This is exact flatness ||tau||^2=p for a nontrivial Dirichlet character.
It does not imply composite-ideal conductor-uniform moment estimates.
-/

noncomputable section
namespace RHLean.Analysis

/-- Individual sqrt(p) Gauss magnitude with native finite-field
orthogonality and no unsupported conjugation lemma. -/
theorem vf919DiscreteSplitPrimeGauss_norm_sq
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) :=
  vf919SplitPrimeGauss_squaredNorm p hp χ hχ

#print axioms vf919DiscreteSplitPrimeGauss_norm_sq

end RHLean.Analysis
