import Mathlib
import «research.STABLE_FAR_RETURNED_RECIPROCAL_FROZEN_WINDOW»
import «research.STABLE_FAR_RETURNED_FIBER_FUBINI»
import «research.AMPLITUDE_GLOBAL_PHYSICAL_DEFECT_LEDGER»

/-!
# AMP physical ledgers on the reciprocal returned-fibre carrier

PRs #718 and #719 put the stable-far renewal on two exact reciprocal
coordinates:

* the literal physical next-child fibre carries the coefficient
  `1/r - sum_q 1/q`;
* the returned `(r,p)` coordinate carries the same reciprocal weighting as a
  frozen-prefix/window packet.

This file first identifies the reciprocal owner weight in those two coordinate
systems cofactor by cofactor.  It then globalizes the local AMP identities from
#717 along a complete descending chronology: the reciprocal Stokes-drop ledger
is exactly the unscaled physical-defect ledger, and the Euler-memory ledger is
exactly the `(p-1)` physical-defect ledger.

Consequently the zero-frequency AMP remainder has the exact pre-square form

  physicalDefectLedger
    + (physicalMemoryLedger - reciprocalQ2MertensColumn).

Thus the remaining arithmetic seam is only the signed finite Fubini which sends
the physical memory ledger through the returned-fibre windows to the reciprocal
q^2 daughter column.  No norm or estimate is introduced here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-! ## Reciprocal physical / returned-coordinate owner bridge -/

/-- On every actual returned cofactor, #718's physical reciprocal owner weight
is exactly the reciprocal sum over #719's returned-coordinate old-owner filter.
This is the pointwise bridge needed before grouping the AMP memory by `(r,p)`. -/
theorem lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_returnedFilter
    {R r p e : ℕ} (hr : r.Prime) (hrR : r < R)
    (hp : p.Prime) (hpR : R + 8 ≤ p)
    (he : e ∈ stableFarReturnedDescendedCofactors R r p) :
    lowWheelFarPrimeQ2CrossingNextReciprocalWeight R (r, (e, p)) =
      ∑ q ∈ (stableFarReturnedOldOwners R r p).filter fun q =>
        e ∈ stableFarReturnedCrossingCofactors R r p q,
        (1 : ℂ) / (q : ℂ) := by
  have hy := stableFarReturnedDescendedCofactor_mem_physical
    hr hrR hp hpR he
  rw [lowWheelFarPrimeQ2CrossingNextReciprocalWeight_eq_ownerSet hy,
    lowWheelFarPrimeQ2CrossingOuterOwnerSet_eq_returnedFilter
      hr hrR hp hpR he]

/-! ## Globalize the AMP Stokes drop and Euler memory on the physical defect -/

/-- The reciprocal Stokes-drop ledger on an evolved stepwise-complete raw
chronology is exactly the chronological unscaled physical-defect ledger. -/
theorem amplitudeReciprocalDropLedger_evolved_eq_physicalDefectLedger
    (R : ℕ) (pre ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R pre ps) :
    amplitudeReciprocalDropLedger R ps
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) =
      amplitudePhysicalDefectLedger R pre ps := by
  induction ps generalizing pre with
  | nil =>
      simp [amplitudeReciprocalDropLedger, amplitudePhysicalDefectLedger]
  | cons p ps ih =>
      rcases hstep with ⟨hp, hcomplete, htail⟩
      have hhead :=
        amplitudeReciprocalDropStep_evolved_eq_amplitudePhysicalDefectStep
          R pre hR hp hcomplete
      have hhead' :
          amplitudeReciprocalDropStep R p
              (squareRootCanonicalRoughAdaptiveCarrier pre
                (Finset.Icc 1 (squareRootEndpoint R)))
              (squareRootCanonicalRoughAdaptiveRawCoefficient pre
                (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) =
            amplitudePhysicalDefectStep R p pre := by
        simpa using hhead
      have htailEq := ih (pre := pre ++ [p]) htail
      simp only [amplitudeReciprocalDropLedger, amplitudePhysicalDefectLedger]
      rw [hhead']
      simpa [squareRootCanonicalRoughAdaptiveCarrier_append,
        squareRootCanonicalRoughAdaptiveRawCoefficient_append,
        squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveRawCoefficient] using htailEq

/-- On a repository-complete descending schedule, the abstract AMP drop ledger
is therefore the literal unscaled physical-defect chronology. -/
theorem correlationReciprocalDropLedger_eq_physicalDefectLedger
    (R : ℕ) (ps : List ℕ) (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    correlationReciprocalDropLedger R ps =
      amplitudePhysicalDefectLedger R [] ps := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  have h :=
    amplitudeReciprocalDropLedger_evolved_eq_physicalDefectLedger
      R [] ps hR hstep
  unfold correlationReciprocalDropLedger
  simpa [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] using h

/-- The Euler-memory ledger on the same evolved raw chronology is exactly the
chronological `(p-1)`-weighted physical-defect ledger. -/
theorem amplitudeEulerMemoryLedger_evolved_eq_physicalMemoryLedger
    (R : ℕ) (pre ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R pre ps) :
    amplitudeEulerMemoryLedger R ps
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) =
      amplitudePhysicalMemoryLedger R pre ps := by
  induction ps generalizing pre with
  | nil =>
      simp [amplitudeEulerMemoryLedger, amplitudePhysicalMemoryLedger]
  | cons p ps ih =>
      rcases hstep with ⟨hp, hcomplete, htail⟩
      have hhead :=
        amplitudeEulerMemoryStep_evolved_eq_sub_one_mul_physicalDefectStep
          R pre hR hp hcomplete
      have hhead' :
          amplitudeEulerMemoryStep R p
              (squareRootCanonicalRoughAdaptiveCarrier pre
                (Finset.Icc 1 (squareRootEndpoint R)))
              (squareRootCanonicalRoughAdaptiveRawCoefficient pre
                (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) =
            ((p : ℂ) - 1) * amplitudePhysicalDefectStep R p pre := by
        simpa using hhead
      have htailEq := ih (pre := pre ++ [p]) htail
      simp only [amplitudeEulerMemoryLedger, amplitudePhysicalMemoryLedger]
      rw [hhead']
      simpa [squareRootCanonicalRoughAdaptiveCarrier_append,
        squareRootCanonicalRoughAdaptiveRawCoefficient_append,
        squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveRawCoefficient] using htailEq

/-- Hence complete-schedule Euler memory is the literal physical memory ledger. -/
theorem correlationEulerMemoryLedger_eq_physicalMemoryLedger
    (R : ℕ) (ps : List ℕ) (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    correlationEulerMemoryLedger R ps =
      amplitudePhysicalMemoryLedger R [] ps := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  have h :=
    amplitudeEulerMemoryLedger_evolved_eq_physicalMemoryLedger
      R [] ps hR hstep
  unfold correlationEulerMemoryLedger
  simpa [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] using h

/-- **Exact AMP frontier on literal physical ledgers.**  The only discrepancy
left after #718/#719 is the signed finite-Fubini identification of physical
Euler memory with the reciprocal q^2 Mertens daughter column. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_physicalDefectLedger_add_memoryGap
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      amplitudePhysicalDefectLedger R [] ps +
        (amplitudePhysicalMemoryLedger R [] ps -
          lowOwnerReciprocalMertensColumn R) := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_dropLedger_add_memoryGap
      R hR ps hsched,
    correlationReciprocalDropLedger_eq_physicalDefectLedger
      R ps (by omega) hsched,
    correlationEulerMemoryLedger_eq_physicalMemoryLedger
      R ps (by omega) hsched]

end RHLean.Proof
