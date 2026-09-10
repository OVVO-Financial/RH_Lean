import Mathlib
import RHLean.Analysis.FinitePrimeTMixing
import RHLean.Arithmetic.PrimeWheelRecoveryScaleIntertwining

/-!
# Exact first-moment action of the 11-layer on the T sector

The finite-prime spectral file records the abstract Walsh factor and the exact
cardinalities of the `11^2` zero-free/no-flip/singleton-flip classes.  Here we
package the same finite arithmetic law directly as an operator on first moments.

For each of the six source/destination sign coordinates, multiplication by the
prime-11 Euler sign has average `19/23` on the `115` zero-free residue classes.
Consequently *every* weight-one linear combination is multiplied by `19/23`,
and its square is multiplied by `(19/23)^2`.

This is a finite deterministic residue identity.  It does not identify the
selected-11 population with the actual all-prime Mobius population; that
intertwining remains a separate physical theorem.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

/-- Sign multiplier contributed by prime `11` to one of the six transition
coordinates.  On the zero-free residue set the coordinate is never divisible by
`11^2`, so divisibility by `11` is exactly the one-prime sign flip. -/
def elevenCoordinateMultiplier (i : Fin 6) (k : Fin 121) : ℚ :=
  if 11 ∣ tTransitionForm i k.1 then -1 else 1

/-- Unnormalized signed multiplier mass on the exact `115`-point zero-free
prime-11 residue population. -/
def elevenCoordinateMultiplierSum (i : Fin 6) : ℚ :=
  ∑ k ∈ elevenZeroFreeResidues, elevenCoordinateMultiplier i k

/-- Every coordinate has signed mass `105 - 10 = 95`: ten zero-free residues
flip that coordinate and the other 105 do not.  We certify the six finite cases
directly from the arithmetic predicates. -/
theorem elevenCoordinateMultiplierSum_eq_ninety_five (i : Fin 6) :
    elevenCoordinateMultiplierSum i = 95 := by
  fin_cases i <;>
    native_decide

/-- Normalized first-moment multiplier on one coordinate. -/
def elevenCoordinateMeanMultiplier (i : Fin 6) : ℚ :=
  elevenCoordinateMultiplierSum i / 115

/-- The direct residue average is the same `19/23` weight-one Walsh factor
already exposed abstractly by `FinitePrimeTMixing`. -/
theorem elevenCoordinateMeanMultiplier_eq_walsh_one (i : Fin 6) :
    elevenCoordinateMeanMultiplier i = onePrimeWalshFactor 11 1 := by
  rw [elevenCoordinateMeanMultiplier,
    elevenCoordinateMultiplierSum_eq_ninety_five,
    onePrimeWalshFactor_eleven_one]
  norm_num

/-- Coordinatewise first-moment action of the exact selected-11 zero-free law. -/
def elevenWeightOneFirstMomentAction (z : Fin 6 → ℚ) : Fin 6 → ℚ :=
  fun i => elevenCoordinateMeanMultiplier i * z i

/-- **Exact scalar action on the whole weight-one sector.**  The six-coordinate
first-moment vector is multiplied coordinatewise by the same `19/23` scalar. -/
theorem elevenWeightOneFirstMomentAction_apply
    (z : Fin 6 → ℚ) (i : Fin 6) :
    elevenWeightOneFirstMomentAction z i =
      onePrimeWalshFactor 11 1 * z i := by
  rw [elevenWeightOneFirstMomentAction,
    elevenCoordinateMeanMultiplier_eq_walsh_one]

/-- Therefore every linear functional of the six weight-one coordinates,
including the Mertens-visible source or destination degree-one combination,
is multiplied by exactly the same scalar. -/
theorem elevenWeightOneFirstMomentAction_linearFunctional
    (a z : Fin 6 → ℚ) :
    (∑ i : Fin 6, a i * elevenWeightOneFirstMomentAction z i) =
      onePrimeWalshFactor 11 1 * (∑ i : Fin 6, a i * z i) := by
  simp only [elevenWeightOneFirstMomentAction_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **Exact rank-one energy contraction.**  Squaring any weight-one first-moment
linear functional multiplies it by `(19/23)^2`.  This is the factor used by the
`q^2` energy renormalization layer. -/
theorem elevenWeightOneFirstMomentAction_linearFunctional_sq
    (a z : Fin 6 → ℚ) :
    (∑ i : Fin 6, a i * elevenWeightOneFirstMomentAction z i) ^ 2 =
      (onePrimeWalshFactor 11 1) ^ 2 *
        (∑ i : Fin 6, a i * z i) ^ 2 := by
  rw [elevenWeightOneFirstMomentAction_linearFunctional]
  ring

/-- The exact square multiplier is strictly subunit. -/
theorem elevenWeightOneFirstMoment_squareFactor_lt_one :
    (onePrimeWalshFactor 11 1) ^ 2 < (1 : ℚ) := by
  rw [onePrimeWalshFactor_eleven_one]
  norm_num

end RHLean.Analysis
