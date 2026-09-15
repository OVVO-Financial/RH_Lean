import Mathlib
import «research.AMPLITUDE_RECIPROCAL_DROP_PHYSICAL_DEFECT»
import «research.DIRECT_SUM_FRESH_PRIME_GLOBAL_COLLAPSE»
import «research.DIRECT_SUM_FRESH_PRIME_STOKES_PRE_SQUARE»

/-!
# Global AMP remainder on the literal physical defect chronology

PR #716 splits the zero-frequency AMP remainder into reciprocal Stokes drop plus
Euler memory, and identifies one local Stokes drop with the existing signed
cofactor-weighted physical defect packet.

This file globalizes that local identification along an actual complete
descending prime schedule.  No norm is taken.

For the evolved state after a processed prefix `pre`, let `D_p(pre)` be the
literal weighted physical defect at the current prime `p`.  Then:

* the reciprocal Stokes drop is exactly `D_p(pre)`;
* the prime-scaled Stokes drop is exactly `p * D_p(pre)`;
* on a complete prefix the Euler-memory step is exactly `(p - 1) * D_p(pre)`;
* the complete canonical rough correlation is the chronological sum
  `sum_p p * D_p(pre)`;
* consequently the zero-frequency AMP remainder is exactly

    sum_p p * D_p(pre) - sum_q M(X_R / q^2) / q.

The final identity is deliberately a gap, not a claimed cancellation.  Its two
prime coordinates are different: `p` is the chronological fresh prime, while
`q` is the low q^2 daughter owner.  The next proof seam is the signed finite
Fubini/transport that relates those coordinates without taking norms early.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Literal cofactor-weighted physical defect produced at the current prime of
an evolved raw chronology. -/
def amplitudePhysicalDefectStep
    (R p : ℕ) (pre : List ℕ) : ℂ :=
  let U0 := Finset.Icc 1 (squareRootEndpoint R)
  let U := squareRootCanonicalRoughAdaptiveCarrier pre U0
  let a := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
    (fun _ => (1 : ℂ))
  let b := fun n : ℕ => (n : ℂ) * a n
  squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b

/-- The local AMP Stokes drop is exactly the literal physical defect step. -/
theorem amplitudeReciprocalDropStep_evolved_eq_amplitudePhysicalDefectStep
    (R : ℕ) {p : ℕ} (pre : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p pre) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier pre U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
      (fun _ => (1 : ℂ))
    amplitudeReciprocalDropStep R p U a =
      amplitudePhysicalDefectStep R p pre := by
  simpa [amplitudePhysicalDefectStep] using
    amplitudeReciprocalDropStep_evolved_eq_physicalDefectMass
      R pre hR hp hcomplete

/-- The prime-weighted Stokes step from the direct-sum chronology is literally
`p` times the same physical defect packet. -/
theorem directSumFreshPrimeScaledReciprocalDrop_eq_prime_mul_physicalDefectStep
    (R : ℕ) {p : ℕ} (pre : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p pre) :
    directSumFreshPrimeScaledReciprocalDrop R p pre =
      (p : ℂ) * amplitudePhysicalDefectStep R p pre := by
  have hdrop :=
    amplitudeReciprocalDropStep_evolved_eq_amplitudePhysicalDefectStep
      R pre hR hp hcomplete
  change (p : ℂ) *
      amplitudeReciprocalDropStep R p
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) =
    (p : ℂ) * amplitudePhysicalDefectStep R p pre
  rw [hdrop]

/-- On a complete prefix the Euler memory retained by the coordinate change is
exactly `(p - 1)` copies of the reciprocal physical defect. -/
theorem amplitudeEulerMemoryStep_evolved_eq_sub_one_mul_physicalDefectStep
    (R : ℕ) {p : ℕ} (pre : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p pre) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier pre U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
      (fun _ => (1 : ℂ))
    amplitudeEulerMemoryStep R p U a =
      ((p : ℂ) - 1) * amplitudePhysicalDefectStep R p pre := by
  dsimp [amplitudeEulerMemoryStep, amplitudePhysicalDefectStep,
    amplitudeEulerCoordinate]
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let U : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier pre U0
  let a : ℕ → ℂ := squareRootCanonicalRoughAdaptiveRawCoefficient pre U0
    (fun _ => (1 : ℂ))
  let b : ℕ → ℂ := fun n => (n : ℂ) * a n
  let nextU := squareRootCanonicalRoughAdaptiveNextCarrier p U
  let E : ℂ := squareRootCanonicalRoughAdaptiveWeightedMass R nextU
    (squareRootCanonicalRoughAdaptiveNextCoefficient p U b)
  let N : ℂ := squareRootCanonicalRoughAdaptiveRawWeightedMass R nextU
    (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)
  let D : ℂ := squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U b
  let B : ℂ := squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a
  have hmemory :=
    evolvedEulerNext_sub_rawNext_eq_one_sub_inv_mul_boundary
      R pre hR hp hcomplete
  dsimp [U0, U, a, b, nextU] at hmemory
  change E - N = (1 - (1 : ℂ) / (p : ℂ)) * B at hmemory
  have hdef :=
    natCast_mul_adaptiveCofactorWeightedPhysicalDefectMass_eq_rawBoundaryMass
      R (p := p) U a hp
  change (p : ℂ) * D = B at hdef
  rw [← hdef] at hmemory
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  change E - N = ((p : ℂ) - 1) * D
  field_simp [hp0] at hmemory ⊢
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmemory

/-- Chronological unscaled physical-defect ledger. -/
def amplitudePhysicalDefectLedger
    (R : ℕ) : List ℕ → List ℕ → ℂ
  | _pre, [] => 0
  | pre, p :: ps =>
      amplitudePhysicalDefectStep R p pre +
        amplitudePhysicalDefectLedger R (pre ++ [p]) ps

/-- Chronological prime-scaled physical-defect ledger. -/
def amplitudeScaledPhysicalDefectLedger
    (R : ℕ) : List ℕ → List ℕ → ℂ
  | _pre, [] => 0
  | pre, p :: ps =>
      (p : ℂ) * amplitudePhysicalDefectStep R p pre +
        amplitudeScaledPhysicalDefectLedger R (pre ++ [p]) ps

/-- Chronological physical Euler-memory ledger. -/
def amplitudePhysicalMemoryLedger
    (R : ℕ) : List ℕ → List ℕ → ℂ
  | _pre, [] => 0
  | pre, p :: ps =>
      ((p : ℂ) - 1) * amplitudePhysicalDefectStep R p pre +
        amplitudePhysicalMemoryLedger R (pre ++ [p]) ps

/-- The direct-sum scaled Stokes ledger is exactly the scaled physical-defect
ledger on every stepwise-complete chronology. -/
theorem directSumFreshPrimeScaledReciprocalDropLedger_eq_scaledPhysicalDefectLedger
    (R : ℕ) (pre ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R pre ps) :
    directSumFreshPrimeScaledReciprocalDropLedger R pre ps =
      amplitudeScaledPhysicalDefectLedger R pre ps := by
  induction ps generalizing pre with
  | nil =>
      simp [directSumFreshPrimeScaledReciprocalDropLedger,
        amplitudeScaledPhysicalDefectLedger]
  | cons p ps ih =>
      rcases hstep with ⟨hp, hcomplete, htail⟩
      have hhead :=
        directSumFreshPrimeScaledReciprocalDrop_eq_prime_mul_physicalDefectStep
          R pre hR hp hcomplete
      have htailEq := ih (pre := pre ++ [p]) htail
      simp only [directSumFreshPrimeScaledReciprocalDropLedger,
        amplitudeScaledPhysicalDefectLedger]
      rw [hhead, htailEq]

/-- Hence the entire rough correlation is a prime-scaled sum of literal
physical defect amplitudes before any square is taken. -/
theorem amplitudeScaledPhysicalDefectLedger_eq_roughCorrelation
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    amplitudeScaledPhysicalDefectLedger R [] ps =
      squareRootCanonicalRoughCorrelation R := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  calc
    amplitudeScaledPhysicalDefectLedger R [] ps =
        directSumFreshPrimeScaledReciprocalDropLedger R [] ps :=
      (directSumFreshPrimeScaledReciprocalDropLedger_eq_scaledPhysicalDefectLedger
        R [] ps (by omega) hstep).symm
    _ = squareRootCanonicalRoughCorrelation R :=
      directSumFreshPrimeScaledReciprocalDropLedger_eq_roughCorrelation
        R hR ps hsched

/-- **Physical-defect normal form of the AMP remainder.**  The entire
zero-frequency remainder is the gap between the prime-scaled physical defect
chronology and the reciprocal low-owner q^2 daughter column.  No memory
identification is assumed. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_scaledPhysicalDefectLedger_sub_reciprocalColumn
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      amplitudeScaledPhysicalDefectLedger R [] ps -
        lowOwnerReciprocalMertensColumn R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    ← amplitudeScaledPhysicalDefectLedger_eq_roughCorrelation R hR ps hsched]

end RHLean.Proof
