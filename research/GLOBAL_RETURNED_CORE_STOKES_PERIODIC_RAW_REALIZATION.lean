import Mathlib
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import «research.GLOBAL_RETURNED_CORE_STOKES_ARBITRARY_CLOCK_WHEEL»

/-!
# Periodic-raw realization of the arbitrary Stokes wheel

This file is still purely algebraic.

The canonical arbitrary-clock wheel zero-pads both the raw comb and the smooth
correction.  That representation is lossless but hides the explicit conductor
structure of the raw comb.  Here we keep the raw seeded comb periodic on the
whole common torus and zero-pad only the smooth correction.  On every physical
prefix the pairing is unchanged.

Because the common Stokes torus contains every local `p^2` period, the DFT of
the periodic raw field is exactly the generic arithmetic conductor coefficient.
Thus the actual corrected prefix has a legal `periodic raw - 2 * pinned smooth`
realization on the same physical clock, before any norm or estimate.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- The natural square-sensitive raw period divides the chosen common torus. -/
theorem lowOwnerStokesSquareSensitivePeriod_dvd_commonTorus
    (R : ℕ) :
    lowOwnerStokesSquareSensitivePeriod R ∣
      lowOwnerStokesCommonTorusModulus R := by
  refine ⟨squareRootEndpoint R + 1, ?_⟩
  unfold lowOwnerStokesCommonTorusModulus
  ring

/-- Every selected local `p^2` period divides the common Stokes torus. -/
theorem lowOwnerStokesPrimeSq_dvd_commonTorus
    {R p : ℕ} (hp : p ∈ lowOwnerStokesWheelPrimes R) :
    p ^ 2 ∣ lowOwnerStokesCommonTorusModulus R :=
  dvd_trans
    (prime_sq_dvd_lowOwnerStokesSquareSensitivePeriod hp)
    (lowOwnerStokesSquareSensitivePeriod_dvd_commonTorus R)

/-- Untruncated raw seeded comb on the common Stokes torus. -/
def lowOwnerStokesPeriodicRawTorusField
    (R : ℕ) (hR : 2 ≤ R) :
    ZMod (lowOwnerStokesWheelSystem R hR).modulus → ℂ :=
  fun z => ((((lowOwnerStokesWheelSystem R hR).rawSite z.val : ℤ) : ℂ))

/-- Actual alternative joint field: periodic raw comb minus the same pinned
smooth-core correction as the canonical finite-wheel realization. -/
def lowOwnerStokesPeriodicRawJointTorusField
    (R : ℕ) (hR : 2 ≤ R) :
    ZMod (lowOwnerStokesWheelSystem R hR).modulus → ℂ :=
  fun z =>
    lowOwnerStokesPeriodicRawTorusField R hR z -
      2 * (lowOwnerStokesWheelSystem R hR).torusSmoothCoreBlockField z

/-- Physical prefix pairing of the alternative joint field. -/
def lowOwnerStokesPeriodicRawPrefixPairing
    (R : ℕ) (hR : 2 ≤ R) (x : ℕ) : ℂ :=
  finiteTorusPairing
    (lowOwnerStokesPeriodicRawJointTorusField R hR)
    ((lowOwnerStokesWheelSystem R hR).torusPrefixWindow x)

/-- On every admissible prefix, periodic raw and zero-padded raw agree after
multiplication by the physical prefix window. -/
theorem lowOwnerStokesPeriodicRawJoint_mul_prefixWindow_eq
    (R : ℕ) (hR : 2 ≤ R) (x : ℕ)
    (hx : x ≤ squareRootEndpoint R)
    (z : ZMod (lowOwnerStokesWheelSystem R hR).modulus) :
    lowOwnerStokesPeriodicRawJointTorusField R hR z *
        (lowOwnerStokesWheelSystem R hR).torusPrefixWindow x z =
      (lowOwnerStokesWheelSystem R hR).torusJointField z *
        (lowOwnerStokesWheelSystem R hR).torusPrefixWindow x z := by
  let W := lowOwnerStokesWheelSystem R hR
  have hjoint :
      W.torusJointField z =
        W.torusRawBlockField z - 2 * W.torusSmoothCoreBlockField z :=
    congrFun (W.torusJointField_eq_raw_sub_two_smooth) z
  rw [hjoint]
  by_cases hwin : W.lower < z.val ∧ z.val ≤ x
  · have hblock : W.lower < z.val ∧ z.val ≤ W.upper := by
      dsimp [W, lowOwnerStokesWheelSystem] at hwin ⊢
      exact ⟨hwin.1, hwin.2.trans hx⟩
    simp [lowOwnerStokesPeriodicRawJointTorusField,
      lowOwnerStokesPeriodicRawTorusField,
      PrimeWheelFiniteSystem.torusPrefixWindow,
      PrimeWheelFiniteSystem.torusRawBlockField,
      W, hwin, hblock]
  · simp [PrimeWheelFiniteSystem.torusPrefixWindow, W, hwin]

/-- The alternative prefix pairing is exactly the canonical torus pairing. -/
theorem lowOwnerStokesPeriodicRawPrefixPairing_eq_torusPrefixPairing
    (R : ℕ) (hR : 2 ≤ R) (x : ℕ)
    (hx : x ≤ squareRootEndpoint R) :
    lowOwnerStokesPeriodicRawPrefixPairing R hR x =
      (lowOwnerStokesWheelSystem R hR).torusPrefixPairing x := by
  classical
  unfold lowOwnerStokesPeriodicRawPrefixPairing
    PrimeWheelFiniteSystem.torusPrefixPairing finiteTorusPairing
  apply Finset.sum_congr rfl
  intro z _hz
  exact lowOwnerStokesPeriodicRawJoint_mul_prefixWindow_eq R hR x hx z

/-- DFT of the untruncated raw field. -/
def lowOwnerStokesPeriodicRawSpectrum
    (R : ℕ) (hR : 2 ≤ R) :
    ZMod (lowOwnerStokesWheelSystem R hR).modulus → ℂ :=
  ZMod.dft (lowOwnerStokesPeriodicRawTorusField R hR)

/-- DFT of the actual periodic-raw-minus-pinned-smooth field. -/
def lowOwnerStokesPeriodicRawJointSpectrum
    (R : ℕ) (hR : 2 ≤ R) :
    ZMod (lowOwnerStokesWheelSystem R hR).modulus → ℂ :=
  ZMod.dft (lowOwnerStokesPeriodicRawJointTorusField R hR)

/-- Exact coefficientwise raw-minus-smooth decomposition in the periodic-raw
realization. -/
theorem lowOwnerStokesPeriodicRawJointSpectrum_eq_raw_sub_two_smooth
    (R : ℕ) (hR : 2 ≤ R)
    (r : ZMod (lowOwnerStokesWheelSystem R hR).modulus) :
    lowOwnerStokesPeriodicRawJointSpectrum R hR r =
      lowOwnerStokesPeriodicRawSpectrum R hR r -
        2 * (lowOwnerStokesWheelSystem R hR).smoothCoreBlockSpectrum r := by
  unfold lowOwnerStokesPeriodicRawJointSpectrum
    lowOwnerStokesPeriodicRawSpectrum
    lowOwnerStokesPeriodicRawJointTorusField
    PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hscalar :
      (∑ z : ZMod (lowOwnerStokesWheelSystem R hR).modulus,
          ZMod.stdAddChar (-(z * r)) *
            (2 * (lowOwnerStokesWheelSystem R hR).torusSmoothCoreBlockField z)) =
        2 * ∑ z : ZMod (lowOwnerStokesWheelSystem R hR).modulus,
          ZMod.stdAddChar (-(z * r)) *
            (lowOwnerStokesWheelSystem R hR).torusSmoothCoreBlockField z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hscalar]

/-- **Explicit conductor constancy of the arbitrary-clock periodic raw DFT.** -/
theorem lowOwnerStokesPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient
    (R : ℕ) (hR : 2 ≤ R)
    (r : ZMod (lowOwnerStokesWheelSystem R hR).modulus) :
    lowOwnerStokesPeriodicRawSpectrum R hR r =
      primeWheelRawConductorArithmeticCoefficient
        (lowOwnerStokesWheelPrimes R)
        (lowOwnerStokesWheelSystem R hR).modulus
        (addOrderOf r) := by
  let W := lowOwnerStokesWheelSystem R hR
  letI : NeZero W.modulus := ⟨Nat.ne_of_gt W.modulus_pos⟩
  unfold lowOwnerStokesPeriodicRawSpectrum
    lowOwnerStokesPeriodicRawTorusField
  change
    ZMod.dft
      (fun z : ZMod W.modulus =>
        (((seededPrimeComb (lowOwnerStokesWheelPrimes R) z.val : ℤ) : ℂ))) r = _
  exact seededPrimeCombDFT_eq_rawConductorArithmeticCoefficient
    (N := W.modulus)
    (lowOwnerStokesWheelPrimes R)
    (fun p hp => lowOwnerStokesWheelPrimes_prime hp)
    (fun p hp => by
      change p ^ 2 ∣ W.modulus
      simpa [W, lowOwnerStokesWheelSystem] using
        lowOwnerStokesPrimeSq_dvd_commonTorus hp)
    r

end RHLean.Proof
