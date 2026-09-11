import Mathlib
import RHLean.Analysis.ElevenWeightOneFirstMoment

/-!
# Actual Möbius / finite-prime tensor compatibility

The exact prime-11 tensor theorem permits an arbitrary field on a *coprime
complementary CRT coordinate*.  It does not permit an arbitrary function of the
same 11^2 coordinate.  The full Möbius/recovered field contains arithmetic from
all other primes, and on a lone 11^2 period that complementary arithmetic is in
general correlated with the 11 residue.

This file gives a direct finite certificate of that distinction on the first
active transition coordinate.  It is a no-go only for the naive substitution of
the full Möbius field into the complementary slot of the 11 tensor theorem; it
does not contradict the tensor theorem itself.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Actual Möbius mass on the first active affine coordinate over one complete
11^2 cell residue period, with 11-square-zero residues removed. -/
def elevenActualMobiusCoordinateMass : ℤ :=
  ∑ k : Fin 121,
    if tSquareZeroFreeAt 11 k.1 then μ (tTransitionForm (0 : Fin 6) k.1) else 0

/-- The same Möbius values after stripping the local first-power 11 sign.  If
this stripped field were independent of the 11^2 coordinate in the sense needed
by the tensor theorem, multiplying the 11 sign back in would produce the exact
19/23 factor. -/
def elevenStrippedMobiusCoordinateMass : ℤ :=
  ∑ k : Fin 121,
    if tSquareZeroFreeAt 11 k.1 then
      (if 11 ∣ tTransitionForm (0 : Fin 6) k.1 then
        -μ (tTransitionForm (0 : Fin 6) k.1)
       else μ (tTransitionForm (0 : Fin 6) k.1))
    else 0

/-- Direct finite arithmetic certificate. -/
theorem elevenActualMobiusCoordinateMass_eq_neg_nine :
    elevenActualMobiusCoordinateMass = -9 := by
  native_decide

/-- Direct finite arithmetic certificate for the stripped complementary mass. -/
theorem elevenStrippedMobiusCoordinateMass_eq_neg_fifteen :
    elevenStrippedMobiusCoordinateMass = -15 := by
  native_decide

/-- **Naive physical tensorization is false.**  On one complete 11^2 residue
period, the actual Möbius complement does not satisfy the selected-prime
weight-one factor `19/23`.  Therefore a proof that contracts the recovered field
must first construct a genuine coprime complementary coordinate (or an exact
signed compensation that removes this correlation). -/
theorem elevenActualMobius_not_weightOneTensor :
    (elevenActualMobiusCoordinateMass : ℚ) ≠
      onePrimeWalshFactor 11 1 *
        (elevenStrippedMobiusCoordinateMass : ℚ) := by
  rw [elevenActualMobiusCoordinateMass_eq_neg_nine,
    elevenStrippedMobiusCoordinateMass_eq_neg_fifteen,
    onePrimeWalshFactor_eleven_one]
  norm_num

/-- The observed one-period multiplier of the actual arithmetic field is 3/5,
not 19/23.  The statement is only a finite diagnostic equality; no limiting
claim is made. -/
theorem elevenActualMobius_onePeriod_ratio :
    (elevenActualMobiusCoordinateMass : ℚ) /
        (elevenStrippedMobiusCoordinateMass : ℚ) = (3 : ℚ) / 5 := by
  rw [elevenActualMobiusCoordinateMass_eq_neg_nine,
    elevenStrippedMobiusCoordinateMass_eq_neg_fifteen]
  norm_num

end RHLean.Analysis
