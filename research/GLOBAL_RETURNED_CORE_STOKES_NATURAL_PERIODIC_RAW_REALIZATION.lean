import Mathlib
import RHLean.Analysis.PrimeWheelPeriodicRawBridge
import RHLean.Analysis.PrimeWheelRawConductorCoefficient
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»

/-!
# Periodic-raw realization on the natural Stokes torus

For `R >= 56` the natural square-sensitive period itself contains the physical
clock.  This file repeats the exact periodic-raw realization on that smaller
torus: leave the seeded raw comb untruncated, zero-pad only the smooth-core
correction, and pair with the same physical prefix window.

The physical prefix pairing is unchanged, while the raw DFT is now taken on the
natural modulus required by the exact conductor product-weight calculus.
No estimate is asserted.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

attribute [local instance] Classical.propDecidable

/-- Untruncated raw seeded comb on the natural Stokes torus. -/
def lowOwnerStokesNaturalPeriodicRawTorusField
    (R : ℕ) (hR : 56 ≤ R) :
    ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus → ℂ :=
  fun z => ((((lowOwnerStokesNaturalWheelSystem R hR).rawSite z.val : ℤ) : ℂ))

/-- Periodic raw comb minus the pinned smooth-core correction. -/
def lowOwnerStokesNaturalPeriodicRawJointTorusField
    (R : ℕ) (hR : 56 ≤ R) :
    ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus → ℂ :=
  fun z =>
    lowOwnerStokesNaturalPeriodicRawTorusField R hR z -
      2 * (lowOwnerStokesNaturalWheelSystem R hR).torusSmoothCoreBlockField z

/-- Physical prefix pairing of the natural periodic-raw realization. -/
def lowOwnerStokesNaturalPeriodicRawPrefixPairing
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) : ℂ :=
  finiteTorusPairing
    (lowOwnerStokesNaturalPeriodicRawJointTorusField R hR)
    ((lowOwnerStokesNaturalWheelSystem R hR).torusPrefixWindow x)

/-- On every physical prefix the natural periodic-raw field and canonical
zero-padded joint field have exactly the same product with the prefix window. -/
theorem lowOwnerStokesNaturalPeriodicRawJoint_mul_prefixWindow_eq
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (hx : x ≤ squareRootEndpoint R)
    (z : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicRawJointTorusField R hR z *
        (lowOwnerStokesNaturalWheelSystem R hR).torusPrefixWindow x z =
      (lowOwnerStokesNaturalWheelSystem R hR).torusJointField z *
        (lowOwnerStokesNaturalWheelSystem R hR).torusPrefixWindow x z := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  have hjoint :
      W.torusJointField z =
        W.torusRawBlockField z - 2 * W.torusSmoothCoreBlockField z :=
    congrFun (W.torusJointField_eq_raw_sub_two_smooth) z
  rw [hjoint]
  by_cases hwin : W.lower < z.val ∧ z.val ≤ x
  · have hblock : W.lower < z.val ∧ z.val ≤ W.upper := by
      dsimp [W, lowOwnerStokesNaturalWheelSystem] at hwin ⊢
      exact ⟨hwin.1, hwin.2.trans hx⟩
    simp [lowOwnerStokesNaturalPeriodicRawJointTorusField,
      lowOwnerStokesNaturalPeriodicRawTorusField,
      PrimeWheelFiniteSystem.torusPrefixWindow,
      PrimeWheelFiniteSystem.torusRawBlockField,
      W, hwin, hblock]
  · simp [PrimeWheelFiniteSystem.torusPrefixWindow, W, hwin]

/-- The natural periodic-raw prefix pairing equals the canonical torus pairing. -/
theorem lowOwnerStokesNaturalPeriodicRawPrefixPairing_eq_torusPrefixPairing
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ)
    (hx : x ≤ squareRootEndpoint R) :
    lowOwnerStokesNaturalPeriodicRawPrefixPairing R hR x =
      (lowOwnerStokesNaturalWheelSystem R hR).torusPrefixPairing x := by
  classical
  unfold lowOwnerStokesNaturalPeriodicRawPrefixPairing
    PrimeWheelFiniteSystem.torusPrefixPairing finiteTorusPairing
  apply Finset.sum_congr rfl
  intro z _hz
  exact lowOwnerStokesNaturalPeriodicRawJoint_mul_prefixWindow_eq
    R hR x hx z

/-- Fourier-side pairing of the same natural periodic-raw joint field. -/
def lowOwnerStokesNaturalPeriodicRawSpectralPrefix
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) : ℂ :=
  finiteTorusSpectralPairing
    (lowOwnerStokesNaturalPeriodicRawJointTorusField R hR)
    ((lowOwnerStokesNaturalWheelSystem R hR).torusPrefixWindow x)

/-- Exact finite Fourier representation of the natural periodic-raw pairing. -/
theorem lowOwnerStokesNaturalPeriodicRawPrefixPairing_eq_spectralPrefix
    (R : ℕ) (hR : 56 ≤ R) (x : ℕ) :
    lowOwnerStokesNaturalPeriodicRawPrefixPairing R hR x =
      lowOwnerStokesNaturalPeriodicRawSpectralPrefix R hR x := by
  exact finiteTorusPairing_eq_spectral
    (lowOwnerStokesNaturalPeriodicRawJointTorusField R hR)
    ((lowOwnerStokesNaturalWheelSystem R hR).torusPrefixWindow x)

/-- Every positive physical prefix of the natural periodic-raw realization is
exactly the same Mertens prefix. -/
theorem lowOwnerStokesNaturalPeriodicRawSpectralPrefix_eq_mertensSummatory
    {R x : ℕ} (hR : 56 ≤ R)
    (hxpos : 0 < x) (hx : x ≤ squareRootEndpoint R) :
    lowOwnerStokesNaturalPeriodicRawSpectralPrefix R hR x =
      mertensSummatory x := by
  rw [← lowOwnerStokesNaturalPeriodicRawPrefixPairing_eq_spectralPrefix]
  rw [lowOwnerStokesNaturalPeriodicRawPrefixPairing_eq_torusPrefixPairing
    R hR x hx]
  have hpair :=
    (lowOwnerStokesNaturalWheelSystem R hR).canonicalTorusRealizationCertificate.pairing_eq_residual
      x hxpos hx
  rw [hpair]
  rw [lowOwnerStokesNaturalWheel_residual_eq_mertensSummatoryInt hR hx]
  exact mertensSummatoryInt_cast x

/-- DFT of the untruncated raw field on the natural torus. -/
def lowOwnerStokesNaturalPeriodicRawSpectrum
    (R : ℕ) (hR : 56 ≤ R) :
    ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus → ℂ :=
  ZMod.dft (lowOwnerStokesNaturalPeriodicRawTorusField R hR)

/-- DFT of the natural periodic-raw-minus-pinned-smooth field. -/
def lowOwnerStokesNaturalPeriodicRawJointSpectrum
    (R : ℕ) (hR : 56 ≤ R) :
    ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus → ℂ :=
  ZMod.dft (lowOwnerStokesNaturalPeriodicRawJointTorusField R hR)

/-- Exact coefficientwise raw-minus-two-smooth decomposition. -/
theorem lowOwnerStokesNaturalPeriodicRawJointSpectrum_eq_raw_sub_two_smooth
    (R : ℕ) (hR : 56 ≤ R)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicRawJointSpectrum R hR r =
      lowOwnerStokesNaturalPeriodicRawSpectrum R hR r -
        2 * (lowOwnerStokesNaturalWheelSystem R hR).smoothCoreBlockSpectrum r := by
  unfold lowOwnerStokesNaturalPeriodicRawJointSpectrum
    lowOwnerStokesNaturalPeriodicRawSpectrum
    lowOwnerStokesNaturalPeriodicRawJointTorusField
    PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hscalar :
      (∑ z : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus,
          ZMod.stdAddChar (-(z * r)) *
            (2 * (lowOwnerStokesNaturalWheelSystem R hR).torusSmoothCoreBlockField z)) =
        2 * ∑ z : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus,
          ZMod.stdAddChar (-(z * r)) *
            (lowOwnerStokesNaturalWheelSystem R hR).torusSmoothCoreBlockField z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  rw [hscalar]

/-- **Explicit conductor constancy on the natural square-sensitive torus.** -/
theorem lowOwnerStokesNaturalPeriodicRawSpectrum_eq_rawConductorArithmeticCoefficient
    (R : ℕ) (hR : 56 ≤ R)
    (r : ZMod (lowOwnerStokesNaturalWheelSystem R hR).modulus) :
    lowOwnerStokesNaturalPeriodicRawSpectrum R hR r =
      primeWheelRawConductorArithmeticCoefficient
        (lowOwnerStokesWheelPrimes R)
        (lowOwnerStokesNaturalWheelSystem R hR).modulus
        (addOrderOf r) := by
  let W := lowOwnerStokesNaturalWheelSystem R hR
  letI : NeZero W.modulus := ⟨Nat.ne_of_gt W.modulus_pos⟩
  unfold lowOwnerStokesNaturalPeriodicRawSpectrum
    lowOwnerStokesNaturalPeriodicRawTorusField
  change
    ZMod.dft
      (fun z : ZMod W.modulus =>
        (((seededPrimeComb (lowOwnerStokesWheelPrimes R) z.val : ℤ) : ℂ))) r = _
  exact seededPrimeCombDFT_eq_rawConductorArithmeticCoefficient
    (N := W.modulus)
    (lowOwnerStokesWheelPrimes R)
    (fun p hp => lowOwnerStokesWheelPrimes_prime hp)
    (fun p hp => by
      simpa [W, lowOwnerStokesNaturalWheelSystem] using
        prime_sq_dvd_lowOwnerStokesNaturalWheelModulus hR hp)
    r

end RHLean.Proof
