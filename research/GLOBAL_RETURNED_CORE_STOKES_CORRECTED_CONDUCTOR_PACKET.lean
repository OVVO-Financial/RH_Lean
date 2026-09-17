import Mathlib
import RHLean.Analysis.CorrectedConductorBoundaryDefectGeneral
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import «research.GLOBAL_RETURNED_CORE_STOKES_PERIODIC_RAW_REALIZATION»

/-!
# Corrected conductor packets on the arbitrary Stokes clock

This file remains entirely before every norm estimate.

For the arbitrary Stokes wheel, the periodic raw DFT is constant on each
reduced-conductor shell with the explicit arithmetic coefficient.  We therefore
factor the raw shell response into that coefficient times the generic
Ramanujan window, retain the pinned smooth correction in the same conductor
packet, and invoke the repository's generic boundary-plus-bulk formulas.

The result is the exact zero-mode fork required by the signed-first program:

* every conductor `c > 1` is boundary-only;
* conductor one has identically zero boundary numerator and is purely bulk.

No conductor is dropped and no magnitude is taken.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- Explicit raw coefficient attached to one conductor of the arbitrary Stokes
wheel. -/
def lowOwnerStokesRawConductorCoefficient
    (R : ℕ) (hR : 2 ≤ R) (c : ℕ) : ℂ :=
  primeWheelRawConductorArithmeticCoefficient
    (lowOwnerStokesWheelPrimes R)
    (lowOwnerStokesWheelSystem R hR).modulus c

/-- Raw periodic contribution carried by one reduced conductor. -/
def lowOwnerStokesPeriodicRawConductorResponse
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesWheelSystem R hR
  ∑ r : ZMod W.modulus,
    if c = reducedAdditiveConductor r then
      (((W.modulus : ℂ)⁻¹) *
        lowOwnerStokesPeriodicRawSpectrum R hR r) *
          W.prefixWindowSpectrum x (-r)
    else 0

/-- Actual corrected conductor packet: periodic raw response minus twice the
pinned smooth-core response. -/
def lowOwnerStokesPeriodicCorrectedConductorResponse
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) : ℂ :=
  lowOwnerStokesPeriodicRawConductorResponse R hR x c -
    2 * primeWheelSmoothConductorResponse
      (lowOwnerStokesWheelSystem R hR) x c

/-- The raw shell response factors exactly through the generic normalized
Ramanujan window. -/
theorem lowOwnerStokesPeriodicRawConductorResponse_eq_coefficient_mul_ramanujanWindow
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) :
    lowOwnerStokesPeriodicRawConductorResponse R hR x c =
      lowOwnerStokesRawConductorCoefficient R hR c *
        primeWheelReducedConductorRamanujanWindow
          (lowOwnerStokesWheelSystem R hR) x c := by
  let W := lowOwnerStokesWheelSystem R hR
  let C := lowOwnerStokesRawConductorCoefficient R hR c
  rw [← primeWheelReducedConductorWindowResponse_eq_ramanujanWindow]
  change lowOwnerStokesPeriodicRawConductorResponse R hR x c =
    C * primeWheelReducedConductorWindowResponse W x c
  unfold lowOwnerStokesPeriodicRawConductorResponse
    primeWheelReducedConductorWindowResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hc : c = reducedAdditiveConductor r
  · simp only [hc, if_true]
    have hraw :=
      lowOwnerStokesPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient
        R hR r
    rw [← reducedAdditiveConductor_eq_addOrderOf W r] at hraw
    have hconst : lowOwnerStokesPeriodicRawSpectrum R hR r = C := by
      simpa [C, lowOwnerStokesRawConductorCoefficient, W, hc] using hraw
    rw [hconst]
    ring
  · simp [hc]

/-- Signed boundary numerator of one corrected conductor packet. -/
def lowOwnerStokesCorrectedConductorBoundaryNumerator
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesWheelSystem R hR
  lowOwnerStokesRawConductorCoefficient R hR c *
      (((conductorBoundaryDefect c 0 W.lower x : ℤ) : ℂ)) -
    2 * (((primeWheelSmoothBoundaryPacket W x c : ℤ) : ℂ))

/-- Signed interval-bulk numerator of one corrected conductor packet. -/
def lowOwnerStokesCorrectedConductorBulkNumerator
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesWheelSystem R hR
  lowOwnerStokesRawConductorCoefficient R hR c *
      (((((Finset.Ioc W.lower x).card : ℤ) *
        (if c = 1 then 1 else 0) : ℤ) : ℂ)) -
    2 * (((primeWheelSmoothBulkMass W *
      ((Finset.Ioc W.lower x).card : ℤ) *
      (if c = 1 then 1 else 0) : ℤ) : ℂ))

/-- **Exact corrected boundary-plus-bulk packet on the actual Stokes clock.** -/
theorem lowOwnerStokesPeriodicCorrectedConductorResponse_eq_boundary_add_bulk
    {R x c : ℕ} (hR : 2 ≤ R)
    (hx : x ≤ squareRootEndpoint R)
    (hcpos : 0 < c)
    (hcmod : c ∣ (lowOwnerStokesWheelSystem R hR).modulus) :
    lowOwnerStokesPeriodicCorrectedConductorResponse R hR x c =
      (((lowOwnerStokesWheelSystem R hR).modulus : ℂ)⁻¹) *
          lowOwnerStokesCorrectedConductorBoundaryNumerator R hR x c +
        (((lowOwnerStokesWheelSystem R hR).modulus : ℂ)⁻¹) *
          lowOwnerStokesCorrectedConductorBulkNumerator R hR x c := by
  let W := lowOwnerStokesWheelSystem R hR
  rw [lowOwnerStokesPeriodicCorrectedConductorResponse,
    lowOwnerStokesPeriodicRawConductorResponse_eq_coefficient_mul_ramanujanWindow]
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary_add_bulk
    W hx hcpos hcmod]
  rw [primeWheelSmoothConductorResponse_eq_boundaryPacket_add_bulk
    W hx hcpos hcmod]
  unfold lowOwnerStokesCorrectedConductorBoundaryNumerator
    lowOwnerStokesCorrectedConductorBulkNumerator conductorBoundaryDefect
  dsimp [W]
  push_cast
  ring

/-- Every nontrivial conductor has no interval bulk at all. -/
theorem lowOwnerStokesCorrectedConductorBulkNumerator_eq_zero_of_one_lt
    (R : ℕ) (hR : 2 ≤ R) (x c : ℕ) (hc : 1 < c) :
    lowOwnerStokesCorrectedConductorBulkNumerator R hR x c = 0 := by
  have hcne : c ≠ 1 := Nat.ne_of_gt hc
  simp [lowOwnerStokesCorrectedConductorBulkNumerator, hcne]

/-- Conductor one has identically zero boundary numerator. -/
theorem lowOwnerStokesCorrectedConductorBoundaryNumerator_one_eq_zero
    (R : ℕ) (hR : 2 ≤ R) (x : ℕ) :
    lowOwnerStokesCorrectedConductorBoundaryNumerator R hR x 1 = 0 := by
  let W := lowOwnerStokesWheelSystem R hR
  have hsmooth : primeWheelSmoothBoundaryPacket W x 1 = 0 := by
    rw [primeWheelSmoothBoundaryPacket_eq_neg_weightedConductorBoundaryDefects]
    simp [conductorBoundaryDefect_one_eq_zero]
  unfold lowOwnerStokesCorrectedConductorBoundaryNumerator
  dsimp [W]
  rw [conductorBoundaryDefect_one_eq_zero, hsmooth]
  simp

/-- Hence every actual conductor `c > 1` is exactly a normalized signed boundary
packet, with raw and smooth terms still coupled. -/
theorem lowOwnerStokesPeriodicCorrectedConductorResponse_eq_boundary_of_one_lt
    {R x c : ℕ} (hR : 2 ≤ R)
    (hx : x ≤ squareRootEndpoint R)
    (hc : 1 < c)
    (hcmod : c ∣ (lowOwnerStokesWheelSystem R hR).modulus) :
    lowOwnerStokesPeriodicCorrectedConductorResponse R hR x c =
      (((lowOwnerStokesWheelSystem R hR).modulus : ℂ)⁻¹) *
        lowOwnerStokesCorrectedConductorBoundaryNumerator R hR x c := by
  rw [lowOwnerStokesPeriodicCorrectedConductorResponse_eq_boundary_add_bulk
    hR hx (Nat.zero_lt_of_lt hc) hcmod]
  rw [lowOwnerStokesCorrectedConductorBulkNumerator_eq_zero_of_one_lt
    R hR x c hc]
  simp

end RHLean.Proof
