import Mathlib
import «research.AMPLITUDE_STOKES_MEMORY_SPLIT»
import RHLean.Proof.PostRootPartnerReciprocalCompression

/-!
# The reciprocal Stokes drop is the existing physical defect

The Stokes-memory split introduces

  RawCurrent - EulerNext

as the reciprocal drop amplitude.  This is not a new analytic object.  On the
actual evolved raw chronology after a complete descending prefix, the compiled
cofactor-weighted reciprocal compression theorem says that the same difference
is exactly the signed physical defect mass already present in the repository.

This file records that identification before any norm.  It is the bridge needed
before one can ask whether the reciprocal-pair `79/81` contraction from #714
controls the squared defect amplitude.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- **Local physical identification of the amplitude drop.**  On the literal
evolved state after a complete descending prefix, the Stokes drop introduced in
the AMP split is exactly the already-compiled cofactor-weighted physical defect
packet. -/
theorem amplitudeReciprocalDropStep_evolved_eq_physicalDefectMass
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    let b := fun n : ℕ => (n : ℂ) * a n
    amplitudeReciprocalDropStep R p U a =
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b := by
  dsimp [amplitudeReciprocalDropStep, amplitudeEulerCoordinate]
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let U : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier qs U0
  let a : ℕ → ℂ := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
    (fun _ => (1 : ℂ))
  let b : ℕ → ℂ := fun n => (n : ℂ) * a n
  have hpos : ∀ n ∈ U, 0 < n := by
    intro n hn
    have hn0 : n ∈ U0 :=
      squareRootCanonicalRoughAdaptiveCarrier_subset qs U0 hn
    have hnRange := Finset.mem_Icc.mp hn0
    omega
  have hcoord :
      squareRootCanonicalRoughAdaptiveRawWeightedMass R U a =
        squareRootCanonicalRoughAdaptiveWeightedMass R U b :=
    adaptiveRawWeightedMass_eq_cofactorWeightedReciprocalMass R U a hpos
  have hstep :=
    cofactorWeighted_evolvedMass_eq_next_add_physicalDefect_of_completeDescendingPrefix
      R qs hR hp hcomplete
  dsimp [U0, U, a, b] at hstep
  change
    squareRootCanonicalRoughAdaptiveRawWeightedMass R U a -
        squareRootCanonicalRoughAdaptiveWeightedMass R
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveNextCoefficient p U b) =
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b
  rw [hcoord, hstep]
  ring

end RHLean.Proof
