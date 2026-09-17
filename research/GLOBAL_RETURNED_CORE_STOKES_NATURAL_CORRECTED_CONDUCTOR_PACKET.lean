import Mathlib
import RHLean.Analysis.CorrectedConductorBoundaryDefectGeneral
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIODIC_RAW_REALIZATION»

/-!
# Corrected conductor packets on the natural Stokes torus

For `R >= 56`, the actual Stokes clock fits inside its natural square-sensitive
period.  The periodic raw DFT on that torus is constant on each reduced
conductor shell with the explicit arithmetic coefficient, so the corrected
`raw - 2 * smooth` packet admits the exact generic Ramanujan boundary-plus-bulk
reduction on the natural modulus itself.

No norm or inequality appears here.
-/

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- Explicit raw coefficient for one conductor of the natural Stokes torus. -/
def lowOwnerStokesNaturalRawConductorCoefficient
    (R : ℕ) (hR : 56 ≤ R) (c : ℕ) : ℂ :=
  primeWheelRawConductorArithmeticCoefficient
    (lowOwnerStokesWheelPrimes R)
    (lowOwnerStokesNaturalWheelSystem R hR).modulus c

/-- Periodic raw contribution carried by one reduced conductor. -/
def lowOwnerStokesNaturalPeriodicRawConductorResponse
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesNaturalWheelSystem R hR
  ∑ r : ZMod W.modulus,
    if c = reducedAdditiveConductor r then
      (((W.modulus : ℂ)⁻¹) *
        lowOwnerStokesNaturalPeriodicRawSpectrum R hR r) *
          W.prefixWindowSpectrum x (-r)
    else 0

/-- Actual corrected conductor packet on the natural torus. -/
def lowOwnerStokesNaturalPeriodicCorrectedConductorResponse
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) : ℂ :=
  lowOwnerStokesNaturalPeriodicRawConductorResponse R hR x c -
    2 * primeWheelSmoothConductorResponse
      (lowOwnerStokesNaturalWheelSystem R hR) x c

/-- The natural raw shell factors exactly through the normalized Ramanujan
window. -/
theorem lowOwnerStokesNaturalPeriodicRawConductorResponse_eq_coefficient_mul_ramanujanWindow
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) :
    lowOwnerStokesNaturalPeriodicRawConductorResponse R hR x c =
      lowOwnerStokesNaturalRawConductorCoefficient R hR c *
        primeWheelReducedConductorRamanujanWindow
          (lowOwnerStokesNaturalWheelSystem R hR) x c := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  let C := lowOwnerStokesNaturalRawConductorCoefficient R hR c
  rw [← primeWheelReducedConductorWindowResponse_eq_ramanujanWindow]
  change lowOwnerStokesNaturalPeriodicRawConductorResponse R hR x c =
    C * primeWheelReducedConductorWindowResponse W x c
  unfold lowOwnerStokesNaturalPeriodicRawConductorResponse
    primeWheelReducedConductorWindowResponse
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hc : c = reducedAdditiveConductor r
  · simp only [hc, if_true]
    have hraw :=
      lowOwnerStokesNaturalPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient
        R hR r
    rw [← reducedAdditiveConductor_eq_addOrderOf W r] at hraw
    have hconst : lowOwnerStokesNaturalPeriodicRawSpectrum R hR r = C := by
      simpa [C, lowOwnerStokesNaturalRawConductorCoefficient, W, hc] using hraw
    rw [hconst]
    ring
  · simp [hc]

/-- Signed boundary numerator of one natural corrected conductor packet. -/
def lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesNaturalWheelSystem R hR
  lowOwnerStokesNaturalRawConductorCoefficient R hR c *
      (((conductorBoundaryDefect c 0 W.lower x : ℤ) : ℂ)) -
    2 * (((primeWheelSmoothBoundaryPacket W x c : ℤ) : ℂ))

/-- Signed interval-bulk numerator of one natural corrected conductor packet. -/
def lowOwnerStokesNaturalCorrectedConductorBulkNumerator
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) : ℂ :=
  let W := lowOwnerStokesNaturalWheelSystem R hR
  lowOwnerStokesNaturalRawConductorCoefficient R hR c *
      (((((Finset.Ioc W.lower x).card : ℤ) *
        (if c = 1 then 1 else 0) : ℤ) : ℂ)) -
    2 * (((primeWheelSmoothBulkMass W *
      ((Finset.Ioc W.lower x).card : ℤ) *
      (if c = 1 then 1 else 0) : ℤ) : ℂ))

/-- **Exact natural-torus corrected boundary-plus-bulk packet.** -/
theorem lowOwnerStokesNaturalPeriodicCorrectedConductorResponse_eq_boundary_add_bulk
    {R x c : ℕ} (hR : 56 ≤ R)
    (hx : x ≤ squareRootEndpoint R)
    (hcpos : 0 < c)
    (hcmod : c ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR x c =
      (((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
          lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator R hR x c +
        (((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
          lowOwnerStokesNaturalCorrectedConductorBulkNumerator R hR x c := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  rw [lowOwnerStokesNaturalPeriodicCorrectedConductorResponse,
    lowOwnerStokesNaturalPeriodicRawConductorResponse_eq_coefficient_mul_ramanujanWindow]
  rw [primeWheelReducedConductorRamanujanWindow_eq_divisorBoundary_add_bulk
    W hx hcpos hcmod]
  rw [primeWheelSmoothConductorResponse_eq_boundaryPacket_add_bulk
    W hx hcpos hcmod]
  unfold lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator
    lowOwnerStokesNaturalCorrectedConductorBulkNumerator conductorBoundaryDefect
  dsimp [W]
  push_cast
  ring

/-- Every nontrivial natural conductor has identically zero interval bulk. -/
theorem lowOwnerStokesNaturalCorrectedConductorBulkNumerator_eq_zero_of_one_lt
    (R : ℕ) (hR : 56 ≤ R) (x c : ℕ) (hc : 1 < c) :
    lowOwnerStokesNaturalCorrectedConductorBulkNumerator R hR x c = 0 := by
  have hcne : c ≠ 1 := Nat.ne_of_gt hc
  simp [lowOwnerStokesNaturalCorrectedConductorBulkNumerator, hcne]

/-- Conductor one has identically zero boundary numerator on the natural torus. -/
theorem lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator_one_eq_zero
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) :
    lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator R hR x 1 = 0 := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  have hsmooth : primeWheelSmoothBoundaryPacket W x 1 = 0 := by
    rw [primeWheelSmoothBoundaryPacket_eq_neg_weightedConductorBoundaryDefects]
    simp [conductorBoundaryDefect_one_eq_zero]
  unfold lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator
  dsimp [W]
  rw [conductorBoundaryDefect_one_eq_zero, hsmooth]
  simp

/-- Hence every natural conductor `c > 1` is exactly a normalized signed
boundary packet, with raw and smooth terms still coupled. -/
theorem lowOwnerStokesNaturalPeriodicCorrectedConductorResponse_eq_boundary_of_one_lt
    {R x c : ℕ} (hR : 56 ≤ R)
    (hx : x ≤ squareRootEndpoint R)
    (hc : 1 < c)
    (hcmod : c ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicCorrectedConductorResponse R hR x c =
      (((lowOwnerStokesNaturalWheelSystem R hR).modulus : ℂ)⁻¹) *
        lowOwnerStokesNaturalCorrectedConductorBoundaryNumerator R hR x c := by
  rw [lowOwnerStokesNaturalPeriodicCorrectedConductorResponse_eq_boundary_add_bulk
    hR hx (Nat.zero_lt_of_lt hc) hcmod]
  rw [lowOwnerStokesNaturalCorrectedConductorBulkNumerator_eq_zero_of_one_lt
    R hR x c hc]
  simp

end RHLean.Proof
