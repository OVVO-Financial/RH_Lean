import Mathlib.Analysis.Fourier.ZMod
import «research.EULER_FRACTIONAL_COUPLED_20261027»

/-!
# Native square-clock nonprincipal cancellation inside the actual Euler floor carrier

For the genuine square clock R^2-1, the two-root shift phase obeys
  (R+h)^2 - R^2 = R*(2*h) + h^2
in every ZMod n.

On any COMPLETE root residue orbit, the signed difference of quadratic
phases is exactly zero whenever 2*h is a nonzero residue. The proof uses
the ordinary integer residue field and Mathlib's additive-character
orthogonality, NOT the imported OpenAI Mertens theorem or any 7/8 growth
bound.

The zero mode, nonprimitive shifts 2*h=0, incomplete root orbit and
the original Mobius coefficient sums remain OPEN. This is an independent
native arithmetic payment on one source-admitted phase sector, not an
improvement of the global zeta zero-free exponent.
-/

noncomputable section
open scoped BigOperators
open AddChar

namespace RHLean.Proof

/-- Actual quadratic square-clock two-root difference, in ZMod n. -/
theorem nativeSquareClock_shift_difference
    {n : ℕ} (R h : ZMod n) :
    (R + h) ^ 2 - R ^ 2 = R * (2 * h) + h ^ 2 := by
  ring

/-- Source-specific complete-residue cancellation for the nonprincipal
    quadratic-root shift. No square-root bound is *assumed*: the complete
    shifted correlation VANISHES EXACTLY by additive-character orthogonality.
    Holds for composite n as well; the exact nonresonance condition is 2h≠0. -/
theorem nativeSquareClock_shift_character_sum_zero
    (n : ℕ) [NeZero n] (h : ZMod n)
    (hNonresonant : (2 : ZMod n) * h ≠ 0) :
    (∑ R : ZMod n,
        ZMod.stdAddChar ((R + h) ^ 2 - R ^ 2)) = 0 := by
  have hOrth :
      (∑ R : ZMod n,
        ZMod.stdAddChar (R * ((2 : ZMod n) * h))) = 0 := by
    have hh := AddChar.sum_mulShift ((2 : ZMod n) * h)
      (ZMod.isPrimitive_stdAddChar n)
    simpa [hNonresonant, ZMod.card] using hh
  calc
    (∑ R : ZMod n,
        ZMod.stdAddChar ((R + h) ^ 2 - R ^ 2)) =
      ∑ R : ZMod n,
        ZMod.stdAddChar (R * ((2 : ZMod n) * h) + h ^ 2) := by
          apply Finset.sum_congr rfl
          intro R _hR
          rw [nativeSquareClock_shift_difference]
    _ = ∑ R : ZMod n,
          ZMod.stdAddChar (R * ((2 : ZMod n) * h)) *
            ZMod.stdAddChar (h ^ 2) := by
          apply Finset.sum_congr rfl
          intro R _hR
          rw [map_add_eq_mul]
    _ = (∑ R : ZMod n,
          ZMod.stdAddChar (R * ((2 : ZMod n) * h))) *
            ZMod.stdAddChar (h ^ 2) := by rw [Finset.sum_mul]
    _ = 0 := by rw [hOrth]; simp

/-- In particular the one-step square clock correlation has no complete
    nonprincipal contribution at any modulus where 2 != 0. -/
theorem nativeSquareClock_adjacent_character_sum_zero
    (n : ℕ) [NeZero n]
    (hTwo : (2 : ZMod n) ≠ 0) :
    (∑ R : ZMod n,
        ZMod.stdAddChar ((R + 1) ^ 2 - R ^ 2)) = 0 := by
  have hNonresonant : (2 : ZMod n) * (1 : ZMod n) ≠ 0 := by
    simpa using hTwo
  exact nativeSquareClock_shift_character_sum_zero n 1 hNonresonant

#print axioms nativeSquareClock_shift_difference
#print axioms nativeSquareClock_shift_character_sum_zero
#print axioms nativeSquareClock_adjacent_character_sum_zero

end RHLean.Proof
