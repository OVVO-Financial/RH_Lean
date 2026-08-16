import RHLean.Arithmetic.PrimeProductLowerBound
import RHLean.Analysis.PrimeWheelRawPeriod
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelLocalSpectrum
import RHLean.Analysis.PrimeWheelPeriodicRawConductorResponse
import RHLean.Analysis.PrimeWheelRawUnitOrbit
import RHLean.Analysis.PrimeWheelRawShellConstancy
import RHLean.Analysis.RamanujanDivisorBoundary
import RHLean.Analysis.PrimeWheelRamanujanIdentification
import RHLean.Analysis.PrimeWheelRamanujanBoundaryReduction
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import RHLean.Analysis.PrimeWheelRawConductorWeight
import RHLean.Analysis.PrimeWheelFullConductorRecombination
import RHLean.Analysis.SmallModulusResonance

/-!
# Periodic-raw conductor attack umbrella

This module collects the exact reductions that replace the oversized zero-padded
raw torus by the natural square-sensitive CRT period on every primorial block
from `k = 2` onward, while preserving the historical corrected residual exactly.

The current layer exposes the exact local `p^2` Fourier trichotomy, the signed
reduced-conductor response, unit-orbit invariance and shell constancy of the
actual periodic raw spectrum, and the identification of every occupied reduced-
conductor character kernel with the classical divisor-form Ramanujan sum.
For every conductor `q > 1`, both the raw interval and every shifted smooth
interval have their common bulk term cancelled exactly, leaving only finite
Möbius-weighted divisor-residue boundary defects.  The remaining common raw
shell Fourier coefficient is also eliminated: it is an exact finite arithmetic
divisor-tail sum indexed by the three local exponents `0,1,2`.

The normalized raw conductor coefficient has an exact local product law.
First-power conductor coordinates cost at most `2/p`, square coordinates cost
exactly `1/p^2`, and the total absolute mass over all exponent patterns is the
finite Euler product `prod_p (1 + 1/p^2)`.  A marked generating identity isolates
the wheel primes not dividing the pinned primorial lower endpoint.  These are
finite structural diagnostics only: they do not by themselves bound the signed
`q > 1` packet.

The full-conductor recombination restores the conductor-one shell before any
norm is taken.  Conductor one is proved to be exactly the additive zero
frequency; the historical corrected residual is then written as that zero atom
plus the explicit divisor-boundary packets over all divisor conductors `q > 1`.
Accordingly, the nonzero response and the `q > 1` packet are auxiliary exact
coordinates, not standalone RH-scale obligations.  The critical path remains
the full corrected residual with zero, raw, and smooth cancellation preserved.

The final lemmas below record a decisive small-modulus diagnostic for that
critical path.  The isolated prime-`3` slot DFT cancels exactly, but restoring
the physical prime-`2` slot factors `1,-1,1` leaves a coherent nonzero residue.
Thus the prime-`3` resonance can only disappear in the full signed corrected
packet, through the smooth correction and/or the remaining conductor channels.

No analytic estimate is claimed here.
-/

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic

/-- The prime-`2` local comb factor attached to physical slot `j`. -/
def physicalPrimeTwoSlotWeight (j : ℕ) : ℤ :=
  localPrimeComb 2 j

@[simp] theorem physicalPrimeTwoSlotWeight_one :
    physicalPrimeTwoSlotWeight 1 = 1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

@[simp] theorem physicalPrimeTwoSlotWeight_two :
    physicalPrimeTwoSlotWeight 2 = -1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

@[simp] theorem physicalPrimeTwoSlotWeight_three :
    physicalPrimeTwoSlotWeight 3 = 1 := by
  norm_num [physicalPrimeTwoSlotWeight, localPrimeComb]

/-- On the actual physical sites `4k+j`, the prime-`2` local factors are
respectively `1,-1,1`. -/
theorem localPrimeComb_two_physical_slots (k : ℕ) :
    localPrimeComb 2 (4 * k + 1) = 1 ∧
      localPrimeComb 2 (4 * k + 2) = -1 ∧
      localPrimeComb 2 (4 * k + 3) = 1 := by
  constructor
  · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
      Nat.add_mod, Nat.mul_mod]
  · constructor
    · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
        Nat.add_mod, Nat.mul_mod]
    · simp [localPrimeComb, pow_two, Nat.dvd_iff_mod_eq_zero,
        Nat.add_mod, Nat.mul_mod]

/-- Restoring the physical prime-`2` factors breaks the isolated cube-root
cancellation: the weighted phase sum is exactly `-2` times the middle phase. -/
theorem physicalPrimeTwoWeightedPrimeThreePhase_sum_eq
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    ((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 1 r +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 2 r +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 3 r =
      (-2 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
  have hphase := physicalPrimeThreeSlotPhase_sum_eq_zero r hr0 hr3
  simp only [physicalPrimeTwoSlotWeight_one,
    physicalPrimeTwoSlotWeight_two, physicalPrimeTwoSlotWeight_three,
    Int.cast_one, Int.cast_neg]
  calc
    1 * physicalPrimeThreeSlotPhase 1 r +
          (-1) * physicalPrimeThreeSlotPhase 2 r +
          1 * physicalPrimeThreeSlotPhase 3 r =
      (physicalPrimeThreeSlotPhase 1 r +
          physicalPrimeThreeSlotPhase 2 r +
          physicalPrimeThreeSlotPhase 3 r) -
        2 * physicalPrimeThreeSlotPhase 2 r := by ring
    _ = (-2 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
      rw [hphase]
      ring

/-- The actual shifted prime-`3` DFT with its physical prime-`2` slot factor
restored. -/
def physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum
    (j : ℕ) (r : ZMod 9) : ℂ :=
  ((physicalPrimeTwoSlotWeight j : ℤ) : ℂ) *
    physicalPrimeThreeLocalRawSlotSpectrum j r

/-- **Exact raw obstruction at conductor three.**  The isolated shifted
prime-`3` DFTs cancel, but after the physical prime-`2` factors are restored the
three-slot raw contribution is the coherent residue `10 * phase₂`, not zero.
Any proof of the full physical bound must therefore cancel this term inside the
joint signed `raw - 2 * smooth` conductor packet (possibly together with other
conductor channels) before taking norms. -/
theorem physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum_sum_eq
    (r : ZMod 9) (hr0 : r ≠ 0) (hr3 : 3 ∣ r.val) :
    physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 1 r +
        physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 2 r +
        physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum 3 r =
      (10 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
  unfold physicalPrimeTwoWeightedPrimeThreeLocalRawSlotSpectrum
  rw [physicalPrimeThreeLocalRawSlotSpectrum_eq_mode,
    physicalPrimeThreeLocalRawSlotSpectrum_eq_mode,
    physicalPrimeThreeLocalRawSlotSpectrum_eq_mode]
  rw [physicalPrimeThreeLocalRawMode_eq_neg_five r hr0 hr3]
  have hweighted :=
    physicalPrimeTwoWeightedPrimeThreePhase_sum_eq r hr0 hr3
  calc
    ((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 1 r * (-5 : ℂ)) +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 2 r * (-5 : ℂ)) +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          (physicalPrimeThreeSlotPhase 3 r * (-5 : ℂ)) =
      (((physicalPrimeTwoSlotWeight 1 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 1 r +
        ((physicalPrimeTwoSlotWeight 2 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 2 r +
        ((physicalPrimeTwoSlotWeight 3 : ℤ) : ℂ) *
          physicalPrimeThreeSlotPhase 3 r) * (-5 : ℂ) := by ring
    _ = (10 : ℂ) * physicalPrimeThreeSlotPhase 2 r := by
      rw [hweighted]
      ring

end RHLean.Analysis
