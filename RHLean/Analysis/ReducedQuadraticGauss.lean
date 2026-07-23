import Mathlib
import RHLean.Analysis.ComplexQuadraticPhase

namespace RHLean.QuadraticPrimePhase

/-- The quadratic phase attached to a unit modulo the corrected modulus `2 * r`.

The unit is evaluated through its canonical `ZMod` representative. Positivity of
`r` supplies the finite `ZMod (2 * r)` instance used by the later unit-group sum.
-/
noncomputable def quadraticUnitPhase
    (a : ℤ) (r : ℕ) (hr : 0 < r)
    (u : (ZMod (2 * r))ˣ) : ℂ := by
  letI : NeZero (2 * r) := ⟨by omega⟩
  exact quadraticPhase a (r : ℤ) (u.val.val : ℤ)

/-- The corrected reduced quadratic Gauss sum.

This sum is taken only over the unit group `(ZMod (2 * r))ˣ`. There is
intentionally no public modulus-`r` version.
-/
noncomputable def reducedQuadraticGauss
    (a : ℤ) (r : ℕ) (hr : 0 < r) : ℂ := by
  letI : NeZero (2 * r) := ⟨by omega⟩
  exact ∑ u : (ZMod (2 * r))ˣ, quadraticUnitPhase a r hr u

/-- The reduced quadratic Gauss factor normalized by `φ(2 * r)`.

The prime-phase factor is complex-valued and remains type-separated from the
rational cell-mask energy appearing elsewhere in the project.
-/
noncomputable def normalizedReducedQuadraticGauss
    (a : ℤ) (r : ℕ) (hr : 0 < r) : ℂ :=
  reducedQuadraticGauss a r hr / (Nat.totient (2 * r) : ℂ)

/-- The normalization denominator is exactly Euler's totient of the corrected modulus. -/
theorem normalizedReducedQuadraticGauss_eq
    (a : ℤ) (r : ℕ) (hr : 0 < r) :
    normalizedReducedQuadraticGauss a r hr =
      reducedQuadraticGauss a r hr / (Nat.totient (2 * r) : ℂ) := by
  rfl

end RHLean.QuadraticPrimePhase
