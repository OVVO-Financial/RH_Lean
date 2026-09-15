import Mathlib
import «research.AMPLITUDE_RETURNED_FIBER_PHYSICAL_BRIDGE»

/-!
# Fixed returned-coordinate physical reciprocal mass

#720 identifies the reciprocal old-owner weight on each actual returned child
with the returned-coordinate owner filter.  This file finishes the finite
Fubini at fixed `(r,p)`: the literal physical reciprocal centered packet is
exactly #719's frozen-window reciprocal packet.

Subtracting it from the already-compiled raw physical centered packet then
produces the exact `(1-1/owner)` Euler-memory window packet.  No norm or
estimate is introduced.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Reciprocal returned mass written directly on the physical descended child
states. -/
def stableFarReturnedPhysicalReciprocalCenteredMass
    (R r p : ℕ) : ℂ :=
  ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
    ((1 : ℂ) / (r : ℂ) -
      lowWheelFarPrimeQ2CrossingNextReciprocalWeight R (r, (e, p))) *
        canonicalMoebiusWeight e

/-- Weighted returned-owner Fubini on the common descended-cofactor carrier. -/
private theorem stableFarReturnedReciprocalCrossingColumn_eq_cofactorWeights
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedReciprocalCrossingColumn R r p =
      ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        lowWheelFarPrimeQ2CrossingNextReciprocalWeight R (r, (e, p)) *
          canonicalMoebiusWeight e := by
  unfold stableFarReturnedReciprocalCrossingColumn
  calc
    (∑ q ∈ stableFarReturnedOldOwners R r p,
        ((1 : ℂ) / (q : ℂ)) *
          (((∑ e ∈ stableFarReturnedCrossingCofactors R r p q, μ e) : ℤ) : ℂ)) =
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then
            ((1 : ℂ) / (q : ℂ)) * canonicalMoebiusWeight e else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [stableFarReturnedCrossingCofactors_eq_descended_filter hr hp hq,
        Finset.sum_filter]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hmem : e ∈ stableFarReturnedCrossingCofactors R r p q
      · simp [hmem, canonicalMoebiusWeight]
      · simp [hmem]
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        ∑ q ∈ stableFarReturnedOldOwners R r p,
          if e ∈ stableFarReturnedCrossingCofactors R r p q then
            ((1 : ℂ) / (q : ℂ)) * canonicalMoebiusWeight e else 0 := by
      exact Finset.sum_comm
    _ = ∑ e ∈ stableFarReturnedDescendedCofactors R r p,
        lowWheelFarPrimeQ2CrossingNextReciprocalWeight R (r, (e, p)) *
          canonicalMoebiusWeight e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_returnedFilter
        hr hrR hp hpR he]
      rw [← Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hq
      rfl

/-- **Physical/arithmetic reciprocal returned-fibre bridge.** -/
theorem stableFarReturnedPhysicalReciprocalCenteredMass_eq_reciprocalCentered
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedPhysicalReciprocalCenteredMass R r p =
      stableFarReturnedReciprocalCenteredMass R r p := by
  unfold stableFarReturnedPhysicalReciprocalCenteredMass
    stableFarReturnedReciprocalCenteredMass
    stableFarReturnedReciprocalDescendedMass
  rw [stableFarReturnedReciprocalCrossingColumn_eq_cofactorWeights
    hr hrR hp hpR]
  unfold stableFarReturnedDescendedMass
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  ring

/-- Raw physical returned centered mass in complex currency. -/
def stableFarReturnedPhysicalUnitCenteredMass
    (R r p : ℕ) : ℂ :=
  ((stableFarReturnedPhysicalCenteredMassInt R r p : ℤ) : ℂ)

/-- The raw physical returned packet is exactly the unit-owner-weight packet. -/
theorem stableFarReturnedPhysicalUnitCenteredMass_eq_ownerWeightedOne
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedPhysicalUnitCenteredMass R r p =
      stableFarReturnedOwnerWeightedCenteredMass (fun _ => (1 : ℂ)) R r p := by
  unfold stableFarReturnedPhysicalUnitCenteredMass
  rw [stableFarReturnedPhysicalCenteredMassInt_eq_centeredMass
    hr hrR hp hpR]
  symm
  exact stableFarReturnedOwnerWeightedCenteredMass_one hr hp

/-- Physical Euler-memory packet at fixed returned coordinates. -/
def stableFarReturnedPhysicalEulerMemoryMass
    (R r p : ℕ) : ℂ :=
  stableFarReturnedPhysicalUnitCenteredMass R r p -
    stableFarReturnedPhysicalReciprocalCenteredMass R r p

/-- **Exact physical Euler-memory normal form.**  Raw unit owner weight minus
reciprocal owner weight is precisely the `(1-1/owner)` frozen-window packet. -/
theorem stableFarReturnedPhysicalEulerMemoryMass_eq_frozenMemoryWindows
    {R r p : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p) :
    stableFarReturnedPhysicalEulerMemoryMass R r p =
      (1 - (1 : ℂ) / (r : ℂ)) *
        ((frozenPrimeUniverseMass (primesUpTo (r - 1))
          (squareRootEndpoint R / (r * r * p)) : ℤ) : ℂ) -
      ∑ q ∈ stableFarReturnedOldOwners R r p,
        (1 - (1 : ℂ) / (q : ℂ)) *
          (((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * r * p)) : ℤ) : ℂ) -
            ((frozenPrimeUniverseMass (primesUpTo (r - 1))
                (squareRootEndpoint R / (q * q * r * p)) : ℤ) : ℂ)) := by
  unfold stableFarReturnedPhysicalEulerMemoryMass
  rw [stableFarReturnedPhysicalUnitCenteredMass_eq_ownerWeightedOne
      hr hrR hp hpR,
    stableFarReturnedPhysicalReciprocalCenteredMass_eq_reciprocalCentered
      hr hrR hp hpR]
  exact stableFarReturned_unit_sub_reciprocal_eq_eulerMemoryWindows hr hp

end RHLean.Proof
