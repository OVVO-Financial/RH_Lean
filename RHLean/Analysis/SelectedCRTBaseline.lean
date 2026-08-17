import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Analysis.OutsidePrimeDeletionMask

/-!
# Selected CRT degree-one baseline

The exact single-outside-prime permutation theorem preserves the complete
selected CRT baseline.  It does not force that uncentered baseline to vanish.
This file identifies the residual baseline exactly in the finite-prime model.

For one generic prime layer the source degree-one observable `a - b + c` has
value

* `1` on the no-flip class;
* `-1, 3, -1` on the three source singleton-flip classes;
* `1, 1, 1` on the three destination singleton-flip classes.

Thus the six equal singleton classes have total degree-one coefficient `4`, and
the one-prime baseline is

`(p^2 - 6p) + 4 (p - 1) = p^2 - 2p - 4`.

Equivalently this is the zero-free mass `p^2 - 6` multiplied by the weight-one
Walsh factor.  Finite independent prime layers therefore multiply the same
nonzero baseline exactly.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Unnormalized degree-one baseline carried by one generic selected-prime
layer.  The coefficient `4` is the signed sum of the six singleton source and
destination degree-one values. -/
def onePrimeDegreeOneBaselineWeight (p : ℕ) : ℚ :=
  onePrimeNoFlipWeight p + 4 * onePrimeSingleFlipWeight p

/-- Closed form of the one-prime unnormalized degree-one baseline. -/
theorem onePrimeDegreeOneBaselineWeight_eq (p : ℕ) :
    onePrimeDegreeOneBaselineWeight p =
      (p : ℚ) ^ 2 - 2 * (p : ℚ) - 4 := by
  unfold onePrimeDegreeOneBaselineWeight onePrimeNoFlipWeight
    onePrimeSingleFlipWeight
  ring

/-- The baseline is exactly zero-free mass times the weight-one Walsh
multiplier.  Thus the finite-prime mixing theorem contracts this mode but does
not annihilate it. -/
theorem onePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh
    {p : ℕ} (hp : 11 ≤ p) :
    onePrimeDegreeOneBaselineWeight p =
      onePrimeZeroFreeWeight p * onePrimeWalshFactor p 1 := by
  rw [onePrimeDegreeOneBaselineWeight_eq, onePrimeWalshFactor_eq hp]
  unfold onePrimeZeroFreeWeight
  have hden : (p : ℚ) ^ 2 - 6 ≠ 0 := by
    have hpos : (0 : ℚ) < (p : ℚ) ^ 2 - 6 := by
      simpa [onePrimeZeroFreeWeight] using onePrimeZeroFreeWeight_pos hp
    exact ne_of_gt hpos
  field_simp [hden]
  ring

/-- Every generic one-prime baseline is strictly positive, hence in particular
is not zero. -/
theorem onePrimeDegreeOneBaselineWeight_pos
    {p : ℕ} (hp : 11 ≤ p) :
    0 < onePrimeDegreeOneBaselineWeight p := by
  rw [onePrimeDegreeOneBaselineWeight_eq]
  have hpq : (11 : ℚ) ≤ (p : ℚ) := by
    exact_mod_cast hp
  nlinarith

/-- At the first generic prime, the raw degree-one baseline is `95`, not zero. -/
@[simp] theorem onePrimeDegreeOneBaselineWeight_eleven :
    onePrimeDegreeOneBaselineWeight 11 = 95 := by
  norm_num [onePrimeDegreeOneBaselineWeight, onePrimeNoFlipWeight,
    onePrimeSingleFlipWeight]

/-- The same `95` baseline normalized by the `115` zero-free residues is the
already-formalized weight-one spectral factor `19/23`. -/
theorem eleven_degreeOneBaseline_ratio_eq_walsh :
    onePrimeDegreeOneBaselineWeight 11 / onePrimeZeroFreeWeight 11 =
      onePrimeWalshFactor 11 1 := by
  norm_num [onePrimeDegreeOneBaselineWeight, onePrimeNoFlipWeight,
    onePrimeSingleFlipWeight, onePrimeZeroFreeWeight]
  exact onePrimeWalshFactor_eleven_one.symm

/-- Product of one-prime zero-free masses for a finite selected family. -/
def finitePrimeZeroFreeMass (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P, onePrimeZeroFreeWeight p

/-- Exact unnormalized degree-one baseline in the finite independent selected
prime product model. -/
def finitePrimeDegreeOneBaselineWeight (P : Finset ℕ) : ℚ :=
  ∏ p ∈ P, onePrimeDegreeOneBaselineWeight p

/-- The finite selected-prime baseline is the zero-free product mass times the
weight-one finite-prime Walsh multiplier. -/
theorem finitePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh
    (P : Finset ℕ) (hP : ∀ p ∈ P, 11 ≤ p) :
    finitePrimeDegreeOneBaselineWeight P =
      finitePrimeZeroFreeMass P * finitePrimeWalshProduct P 1 := by
  classical
  unfold finitePrimeDegreeOneBaselineWeight finitePrimeZeroFreeMass
    finitePrimeWalshProduct
  calc
    (∏ p ∈ P, onePrimeDegreeOneBaselineWeight p) =
        ∏ p ∈ P,
          (onePrimeZeroFreeWeight p * onePrimeWalshFactor p 1) := by
      apply Finset.prod_congr rfl
      intro p hpMem
      exact onePrimeDegreeOneBaselineWeight_eq_zeroFree_mul_walsh
        (hP p hpMem)
    _ = (∏ p ∈ P, onePrimeZeroFreeWeight p) *
          ∏ p ∈ P, onePrimeWalshFactor p 1 := by
      rw [Finset.prod_mul_distrib]

/-- The raw finite selected-prime baseline never vanishes for an admissible
finite prime family.  Exact CRT deletion invariance therefore preserves a
coherent residual baseline rather than an identically zero mode. -/
theorem finitePrimeDegreeOneBaselineWeight_pos
    (P : Finset ℕ) (hP : ∀ p ∈ P, 11 ≤ p) :
    0 < finitePrimeDegreeOneBaselineWeight P := by
  unfold finitePrimeDegreeOneBaselineWeight
  apply Finset.prod_pos
  intro p hpMem
  exact onePrimeDegreeOneBaselineWeight_pos (hP p hpMem)

/-- Explicit nonvanishing form, useful when ruling out a false zero-baseline
recombination theorem. -/
theorem finitePrimeDegreeOneBaselineWeight_ne_zero
    (P : Finset ℕ) (hP : ∀ p ∈ P, 11 ≤ p) :
    finitePrimeDegreeOneBaselineWeight P ≠ 0 :=
  ne_of_gt (finitePrimeDegreeOneBaselineWeight_pos P hP)

end RHLean.Analysis
