import Mathlib
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelHarmonicCriterion

/-!
# Conductor packets for the periodic-raw realization

After the natural-period reduction, the actual corrected primorial-wheel
residual has a second exact spectral realization in which the raw seeded comb is
left periodic and only the smooth correction is zero-padded.  This file groups
that exact response by reduced additive conductor before taking any norm.

The raw and smooth terms are kept in the same conductor packet, and every
packet satisfies an exact `raw - 2 * smooth` identity.  These are finite
regrouping theorems only; no cancellation estimate is asserted.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- One frequency atom for the periodic raw spectrum. -/
def primorialPeriodicRawSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    primorialPeriodicRawSpectrum k r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- One frequency atom for the zero-padded smooth correction. -/
def primorialPeriodicSmoothSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    (primorialMinimalWheelSystem k).smoothCoreBlockSpectrum r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- One frequency atom for the actual signed periodic-raw joint spectrum. -/
def primorialPeriodicRawJointSpectralAtom
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) : ℂ :=
  ((((primorialMinimalWheelSystem k).modulus : ℂ)⁻¹) *
    primorialPeriodicRawJointSpectrum k r) *
      (primorialMinimalWheelSystem k).prefixWindowSpectrum x (-r)

/-- The signed raw/smooth subtraction is retained at each individual frequency. -/
theorem primorialPeriodicRawJointSpectralAtom_eq_raw_sub_two_smooth
    (k x : ℕ)
    (r : ZMod (primorialMinimalWheelSystem k).modulus) :
    primorialPeriodicRawJointSpectralAtom k x r =
      primorialPeriodicRawSpectralAtom k x r -
        2 * primorialPeriodicSmoothSpectralAtom k x r := by
  rw [primorialPeriodicRawJointSpectrum_eq_raw_sub_two_smooth]
  unfold primorialPeriodicRawJointSpectralAtom
    primorialPeriodicRawSpectralAtom primorialPeriodicSmoothSpectralAtom
  ring

/-- The complete periodic-raw spectral prefix is the sum of its frequency atoms. -/
theorem primorialPeriodicRawSpectralPrefix_eq_sum_atoms
    (k x : ℕ) :
    primorialPeriodicRawSpectralPrefix k x =
      ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
        primorialPeriodicRawJointSpectralAtom k x r := by
  unfold primorialPeriodicRawSpectralPrefix finiteTorusSpectralPairing
    primorialPeriodicRawJointSpectralAtom
    primorialPeriodicRawJointSpectrum
    PrimeWheelFiniteSystem.prefixWindowSpectrum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Raw contribution carried by one reduced additive conductor. -/
def primorialPeriodicRawConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicRawSpectralAtom k x r
    else 0

/-- Smooth-core contribution carried by the same reduced additive conductor. -/
def primorialPeriodicSmoothConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicSmoothSpectralAtom k x r
    else 0

/-- Actual corrected contribution carried by one reduced additive conductor. -/
def primorialPeriodicRawJointConductorResponse
    (k x q : ℕ) : ℂ :=
  ∑ r : ZMod (primorialMinimalWheelSystem k).modulus,
    if q = reducedAdditiveConductor r then
      primorialPeriodicRawJointSpectralAtom k x r
    else 0

/-- Every conductor packet preserves the exact signed raw-minus-smooth
interaction before any norm or triangle inequality is introduced. -/
theorem primorialPeriodicRawJointConductorResponse_eq_raw_sub_two_smooth
    (k x q : ℕ) :
    primorialPeriodicRawJointConductorResponse k x q =
      primorialPeriodicRawConductorResponse k x q -
        2 * primorialPeriodicSmoothConductorResponse k x q := by
  classical
  unfold primorialPeriodicRawJointConductorResponse
    primorialPeriodicRawConductorResponse
    primorialPeriodicSmoothConductorResponse
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hq : q = reducedAdditiveConductor r
  · simp only [hq, if_true]
    rw [primorialPeriodicRawJointSpectralAtom_eq_raw_sub_two_smooth]
    ring
  · simp [hq]

/-- Exact conductor partition of the complete actual periodic-raw response. -/
theorem primorialPeriodicRawSpectralPrefix_eq_sum_conductorResponses
    (k x : ℕ) :
    primorialPeriodicRawSpectralPrefix k x =
      ∑ q ∈ Finset.range ((primorialMinimalWheelSystem k).modulus + 1),
        primorialPeriodicRawJointConductorResponse k x q := by
  classical
  rw [primorialPeriodicRawSpectralPrefix_eq_sum_atoms]
  unfold primorialPeriodicRawJointConductorResponse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hcond :
      reducedAdditiveConductor r ≤ (primorialMinimalWheelSystem k).modulus := by
    unfold reducedAdditiveConductor
    split_ifs
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (primorialMinimalWheelSystem k).modulus_pos)
    · exact Nat.div_le_self _ _
  have hmem :
      reducedAdditiveConductor r ∈
        Finset.range ((primorialMinimalWheelSystem k).modulus + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hcond)
  simp [hmem]

/-- The historical corrected residual therefore has an exact signed conductor
expansion in the periodic-raw coordinates. -/
theorem primorialPeriodicRawResidual_eq_sum_conductorResponses
    (k : ℕ) {x : ℕ}
    (hlower : primorialBlockLower k < x)
    (hupper : x ≤ primorialBlockUpper k) :
    ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) =
      ∑ q ∈ Finset.range ((primorialMinimalWheelSystem k).modulus + 1),
        primorialPeriodicRawJointConductorResponse k x q := by
  rw [← primorialPeriodicRawSpectralPrefix_eq_residual k hlower hupper]
  exact primorialPeriodicRawSpectralPrefix_eq_sum_conductorResponses k x

end RHLean.Analysis
