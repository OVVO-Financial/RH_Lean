import Mathlib
import RHLean.Arithmetic.PrimorialWheelScale
import RHLean.Analysis.PrimeWheelJointSpectrum
import RHLean.Analysis.PrimeWheelTorusRealization

/-!
# Periodic raw-field realization of primorial-wheel prefixes

The canonical torus realization zero-pads the whole corrected arithmetic block.
That is ideal for the lossless residual identity, but it hides the complete
periodic CRT spectrum of the raw seeded prime comb.

For the concrete primorial wheel we may instead leave the raw comb untruncated
on the common torus and zero-pad only the smooth-core correction.  The pinned
prefix window is supported inside the arithmetic block, so this alternative
field has exactly the same pairing with every admissible prefix window.  Thus it
is another exact Fourier realization of the actual corrected residual, while
retaining the periodic raw field needed for the complete CRT/conductor analysis.

This file establishes only exact finite identities.  It makes no analytic
estimate.
-/

open scoped BigOperators

noncomputable section

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Arithmetic.PrimeWheelFiniteSystem

/-- The raw seeded prime comb left untruncated on the common primorial torus. -/
def primorialPeriodicRawTorusField
    (k : ℕ) : ZMod (primorialWheelSystem k).modulus → ℂ :=
  fun z => ((((primorialWheelSystem k).rawSite z.val : ℤ) : ℂ))

/-- Alternative joint torus field: periodic raw comb minus the same zero-padded
smooth-core correction used by the canonical block realization. -/
def primorialPeriodicRawJointTorusField
    (k : ℕ) : ZMod (primorialWheelSystem k).modulus → ℂ :=
  fun z =>
    primorialPeriodicRawTorusField k z -
      2 * (primorialWheelSystem k).torusSmoothCoreBlockField z

/-- Pair the alternative field with the same pinned arithmetic prefix window. -/
def primorialPeriodicRawPrefixPairing
    (k x : ℕ) : ℂ :=
  finiteTorusPairing
    (primorialPeriodicRawJointTorusField k)
    ((primorialWheelSystem k).torusPrefixWindow x)

/-- On every admissible prefix, the alternative periodic-raw field and the
canonical zero-padded joint field agree after multiplication by the prefix
window.  Outside the window both products vanish; inside it the raw block field
is exactly the untruncated raw site. -/
theorem primorialPeriodicRawJoint_mul_prefixWindow_eq
    (k x : ℕ)
    (hupper : x ≤ (primorialWheelSystem k).upper)
    (z : ZMod (primorialWheelSystem k).modulus) :
    primorialPeriodicRawJointTorusField k z *
        (primorialWheelSystem k).torusPrefixWindow x z =
      (primorialWheelSystem k).torusJointField z *
        (primorialWheelSystem k).torusPrefixWindow x z := by
  have hjoint :
      (primorialWheelSystem k).torusJointField z =
        (primorialWheelSystem k).torusRawBlockField z -
          2 * (primorialWheelSystem k).torusSmoothCoreBlockField z :=
    congrFun
      ((primorialWheelSystem k).torusJointField_eq_raw_sub_two_smooth) z
  rw [hjoint]
  by_cases hwin :
      (primorialWheelSystem k).lower < z.val ∧ z.val ≤ x
  · have hblock :
        (primorialWheelSystem k).lower < z.val ∧
          z.val ≤ (primorialWheelSystem k).upper :=
      ⟨hwin.1, hwin.2.trans hupper⟩
    simp [primorialPeriodicRawJointTorusField,
      primorialPeriodicRawTorusField,
      PrimeWheelFiniteSystem.torusPrefixWindow,
      PrimeWheelFiniteSystem.torusRawBlockField,
      hwin, hblock]
  · simp [PrimeWheelFiniteSystem.torusPrefixWindow, hwin]

/-- The periodic-raw pairing is exactly the canonical torus prefix pairing. -/
theorem primorialPeriodicRawPrefixPairing_eq_torusPrefixPairing
    (k x : ℕ)
    (hupper : x ≤ (primorialWheelSystem k).upper) :
    primorialPeriodicRawPrefixPairing k x =
      (primorialWheelSystem k).torusPrefixPairing x := by
  classical
  unfold primorialPeriodicRawPrefixPairing
    PrimeWheelFiniteSystem.torusPrefixPairing
    finiteTorusPairing
  apply Finset.sum_congr rfl
  intro z hz
  exact primorialPeriodicRawJoint_mul_prefixWindow_eq k x hupper z

/-- Hence the periodic-raw torus realizes the actual arithmetic wheel residual
on every nonempty pinned prefix. -/
theorem primorialPeriodicRawPrefixPairing_eq_residual
    (k : ℕ) {x : ℕ}
    (hlower : (primorialWheelSystem k).lower < x)
    (hupper : x ≤ (primorialWheelSystem k).upper) :
    primorialPeriodicRawPrefixPairing k x =
      ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) := by
  rw [primorialPeriodicRawPrefixPairing_eq_torusPrefixPairing k x hupper]
  exact
    (primorialWheelSystem k).canonicalTorusRealizationCertificate.pairing_eq_residual
      x hlower hupper

/-- Fourier-side pairing of the same alternative field and prefix window. -/
def primorialPeriodicRawSpectralPrefix
    (k x : ℕ) : ℂ :=
  finiteTorusSpectralPairing
    (primorialPeriodicRawJointTorusField k)
    ((primorialWheelSystem k).torusPrefixWindow x)

/-- The alternative periodic-raw prefix pairing has the exact finite Fourier
representation on the common torus. -/
theorem primorialPeriodicRawPrefixPairing_eq_spectralPrefix
    (k x : ℕ) :
    primorialPeriodicRawPrefixPairing k x =
      primorialPeriodicRawSpectralPrefix k x := by
  exact finiteTorusPairing_eq_spectral
    (primorialPeriodicRawJointTorusField k)
    ((primorialWheelSystem k).torusPrefixWindow x)

/-- The periodic-raw spectral prefix is therefore another exact spectral
representation of the actual corrected wheel residual. -/
theorem primorialPeriodicRawSpectralPrefix_eq_residual
    (k : ℕ) {x : ℕ}
    (hlower : (primorialWheelSystem k).lower < x)
    (hupper : x ≤ (primorialWheelSystem k).upper) :
    primorialPeriodicRawSpectralPrefix k x =
      ((((primorialWheelSystem k).residual x : ℤ) : ℂ)) := by
  rw [← primorialPeriodicRawPrefixPairing_eq_spectralPrefix k x]
  exact primorialPeriodicRawPrefixPairing_eq_residual k hlower hupper

/-- DFT of the untruncated raw field on the common torus.  The next CRT bridge
will identify this transform with the sparse lift of the complete natural-period
raw spectrum. -/
def primorialPeriodicRawSpectrum
    (k : ℕ) : ZMod (primorialWheelSystem k).modulus → ℂ :=
  ZMod.dft (primorialPeriodicRawTorusField k)

/-- DFT of the alternative actual joint field. -/
def primorialPeriodicRawJointSpectrum
    (k : ℕ) : ZMod (primorialWheelSystem k).modulus → ℂ :=
  ZMod.dft (primorialPeriodicRawJointTorusField k)

/-- Exact coefficientwise signed decomposition for the alternative spectrum.
Unlike the zero-padded raw-block transform, the first term here is the DFT of
the full periodic raw comb. -/
theorem primorialPeriodicRawJointSpectrum_eq_raw_sub_two_smooth
    (k : ℕ) (r : ZMod (primorialWheelSystem k).modulus) :
    primorialPeriodicRawJointSpectrum k r =
      primorialPeriodicRawSpectrum k r -
        2 * (primorialWheelSystem k).smoothCoreBlockSpectrum r := by
  unfold primorialPeriodicRawJointSpectrum primorialPeriodicRawSpectrum
    primorialPeriodicRawJointTorusField
    PrimeWheelFiniteSystem.smoothCoreBlockSpectrum
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hscalar :
      (∑ x : ZMod (primorialWheelSystem k).modulus,
          ZMod.stdAddChar (-(x * r)) *
            (2 * (primorialWheelSystem k).torusSmoothCoreBlockField x)) =
        2 * ∑ x : ZMod (primorialWheelSystem k).modulus,
          ZMod.stdAddChar (-(x * r)) *
            (primorialWheelSystem k).torusSmoothCoreBlockField x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hscalar]

end RHLean.Analysis
