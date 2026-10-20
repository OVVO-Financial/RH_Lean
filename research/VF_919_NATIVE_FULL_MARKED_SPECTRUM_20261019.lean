import «research.VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP»
import «research.VF_MID_919_OAI_SIGNED_SIXTH_POWER_INLET»
import «research.VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION»

/-!
# Native all-selected-prime marked spectrum on genuine Möbius owner sites

This is a full finite-subset identity on RH_Lean's OWN scalar source:
  - `lowOwnerZeroFrequencyMobiusSite` is the original returned-core owner
    weight times the literal integer Moebius sign.
  - smooth and transported source masks use the native exact S=A-T.
  - a labeled prime-slot amplifier retains repeated ideal norms as
    DIFFERENT labels, full subsets, their signs, and physical dilations.

No OAI analytic theorem, nonvanishing theorem, character moment, or
conditional Mertens exponent enters these source identities. The complete
holomorphic Hecke detector and uniform moment savings are distinct objects;
the equalities below do not claim those estimates.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
attribute [local instance] Classical.propDecidable

/-- Actual signed Mobius population inside the native smooth sector. -/
def vf919MarkedNativeSmoothSource (R X n : ℕ) : ℂ :=
  (lowOwnerZeroFrequencyMobiusSite R n : ℂ) *
    vf919SmoothPhysicalWeight R X n

/-- Actual signed Mobius population inside the native high-owner sector.
    Its sign is the already-compiled S=A-T convention, not reoriented. -/
def vf919MarkedNativeHighSource (R X n : ℕ) : ℂ :=
  (lowOwnerZeroFrequencyMobiusSite R n : ℂ) *
    vf919HighTransportPhysicalWeight R X n

/-- Exact original sharp site after complete smooth-minus-high reassembly. -/
def vf919MarkedNativeSharpSource (R X n : ℕ) : ℂ :=
  (lowOwnerZeroFrequencyMobiusSite R n : ℂ) *
    vf919SharpPhysicalWeight X n

/-- Pointwise native S=A-T, including original signed site weights. -/
theorem vf919MarkedNativeSmooth_sub_high_eq_sharp
    (R X : ℕ) :
    (fun n => vf919MarkedNativeSmoothSource R X n -
      vf919MarkedNativeHighSource R X n) =
        vf919MarkedNativeSharpSource R X := by
  funext n
  unfold vf919MarkedNativeSmoothSource vf919MarkedNativeHighSource
    vf919MarkedNativeSharpSource
  have h := congrFun (vf919Smooth_sub_transport_eq_sharp R X) n
  change vf919SmoothPhysicalWeight R X n -
    vf919HighTransportPhysicalWeight R X n =
    vf919SharpPhysicalWeight X n at h
  rw [← mul_sub, h]

/-- Entire labeled squarefree prime-slot row is additive IN THE PHYSICAL
    WEIGHT. All subsets and primes are retained, not estimated separately. -/
theorem vf919NativeFiniteIdealRow_sub
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (norm : ι → ℕ) (phase : ι → ℂ)
    (u v : ℕ → ℂ) :
    vf919FiniteIdealRow P norm phase (fun n => u n - v n) =
      vf919FiniteIdealRow P norm phase u -
        vf919FiniteIdealRow P norm phase v := by
  unfold vf919FiniteIdealRow
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

/-- ALL finite marked-minus-rescaled prime subsets on the genuine native
    S=A-T source. The right is the complete signed divisor/amplifier
    expansion; actual physical weights are evaluated at the dilated norm,
    not approximated by a product of independent factors. -/
theorem vf919NativeFullMarkedSpectrum_sourceIdentity
    {ι : Type*} [DecidableEq ι]
    (P A : Finset ι) (hA : A ⊆ P)
    (norm : ι → ℕ) (phase : ι → ℂ) (R X : ℕ) :
    vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeSmoothSource R X) -
      vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeHighSource R X) =
      ∑ d ∈ A.powerset, vf919IdealLabelCoefficient phase d *
        vf919SixthPowerMaskedRow P A norm phase
          (vf919NormDilatedWeight norm d
            (vf919MarkedNativeSharpSource R X)) := by
  rw [← vf919NativeFiniteIdealRow_sub]
  rw [vf919MarkedNativeSmooth_sub_high_eq_sharp R X]
  exact vf919FiniteIdealRow_sixthPower_column P A hA norm phase
    (vf919MarkedNativeSharpSource R X)

/-- Total complex covariance, including every diagonal, mixed phase, and
    source/transport cross-term. This is the exact signed decomposition
    before any moment inequality, not the sum of independent source norms. -/
theorem vf919NativeFullMarkedSpectrum_signedHermitianEnergy
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (norm : ι → ℕ) (phase : ι → ℂ) (R X : ℕ) :
    ‖vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeSharpSource R X)‖ ^ 2 =
      ‖vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeSmoothSource R X)‖ ^ 2 +
      ‖vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeHighSource R X)‖ ^ 2 -
      2 * (vf919FiniteIdealRow P norm phase
          (vf919MarkedNativeSmoothSource R X) *
        star (vf919FiniteIdealRow P norm phase
          (vf919MarkedNativeHighSource R X))).re := by
  have hsource :=
    vf919NativeFiniteIdealRow_sub P norm phase
      (vf919MarkedNativeSmoothSource R X)
      (vf919MarkedNativeHighSource R X)
  rw [vf919MarkedNativeSmooth_sub_high_eq_sharp R X] at hsource
  rw [hsource]
  simpa [Complex.sq_norm] using
    Complex.normSq_sub
      (vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeSmoothSource R X))
      (vf919FiniteIdealRow P norm phase
        (vf919MarkedNativeHighSource R X))

#print axioms vf919MarkedNativeSmooth_sub_high_eq_sharp
#print axioms vf919NativeFiniteIdealRow_sub
#print axioms vf919NativeFullMarkedSpectrum_sourceIdentity
#print axioms vf919NativeFullMarkedSpectrum_signedHermitianEnergy

end RHLean.Proof
