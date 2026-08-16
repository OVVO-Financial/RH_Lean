import Mathlib
import RHLean.Analysis.PrimeWheelFullConductorUniformPacket

/-!
# Full corrected conductor-three packet

This module specializes the signed periodic-raw conductor packet to reduced
additive conductor `3`.  At this conductor the divisor `1` boundary vanishes,
so both raw and smooth terms are pure mod-`3` endpoint defects before any norm
is taken.

The purpose is to test the dangerous local prime-`3` resonance in the full
`raw - 2 * smooth` arithmetic packet rather than in the raw local DFT alone.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- A modulus-one divisor boundary is identically zero. -/
theorem divisorIntervalBoundary_one_eq_zero
    (a lower upper : ℕ) :
    divisorIntervalBoundary 1 a lower upper = 0 := by
  unfold divisorIntervalBoundary divisorResidueBoundary divisorResidueCount
  simp [Nat.ModEq]

/-- The conductor-three Möbius divisor packet has only its mod-`3` boundary
term; the divisor-one term vanishes exactly. -/
theorem conductorThree_divisorBoundaryPacket_eq
    (a lower upper : ℕ) :
    (∑ d ∈ (3 : ℕ).divisors,
      μ (3 / d) * divisorIntervalBoundary d a lower upper) =
      divisorIntervalBoundary 3 a lower upper := by
  norm_num [Nat.divisors, divisorIntervalBoundary_one_eq_zero]

/-- The smooth conductor-three packet is exactly the signed sum of mod-`3`
boundary defects over the actual smooth divisor sites. -/
theorem primeWheelSmoothBoundaryPacket_three
    (W : PrimeWheelFiniteSystem) (x : ℕ) :
    primeWheelSmoothBoundaryPacket W x 3 =
      ∑ a ∈ primeWheelSmoothDivisorSites W,
        -(μ a) * divisorIntervalBoundary 3 a W.lower x := by
  classical
  unfold primeWheelSmoothBoundaryPacket
  apply Finset.sum_congr rfl
  intro a ha
  rw [conductorThree_divisorBoundaryPacket_eq]

/-- **Exact full corrected conductor-three packet.**  Once conductor `3` is an
actual divisor of the primorial torus, the full `raw - 2 * smooth` response is
one common torus normalization multiplying only mod-`3` endpoint boundary
defects.  In particular no growing conductor-three bulk survives. -/
theorem primorialPeriodicRawJointConductorResponse_three_eq_boundary
    (k x : ℕ)
    (h3mem : 3 ∈ (primorialMinimalWheelSystem k).modulus.divisors)
    (hx : x ≤ (primorialMinimalWheelSystem k).upper) :
    primorialPeriodicRawJointConductorResponse k x 3 =
      (((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
        (primorialRawConductorArithmeticCoefficient k 3 *
            (((divisorIntervalBoundary 3 0
              (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ)) +
          2 * (((∑ a ∈ primeWheelSmoothDivisorSites
                (primorialMinimalWheelSystem k),
              μ a * divisorIntervalBoundary 3 a
                (primorialMinimalWheelSystem k).lower x : ℤ) : ℂ))) := by
  rw [primorialPeriodicRawJointConductorResponse_eq_explicitAllConductor
    k x 3 h3mem hx]
  unfold primorialPeriodicRawExplicitAllConductorPacket
  rw [conductorThree_divisorBoundaryPacket_eq]
  rw [primeWheelSmoothBoundaryPacket_three]
  norm_num
  push_cast
  ring

end RHLean.Analysis
