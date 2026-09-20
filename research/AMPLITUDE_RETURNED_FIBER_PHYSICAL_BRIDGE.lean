import Mathlib
import «research.STABLE_FAR_RETURNED_RECIPROCAL_FROZEN_WINDOW»
import «research.STABLE_FAR_RETURNED_FIBER_FUBINI»
import «research.AMPLITUDE_GLOBAL_PHYSICAL_DEFECT_LEDGER»
import «research.CANONICAL_DESCENDING_PRIME_CHRONOLOGY»

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

/-! ## Canonical closure reduction -/

/-- The prime-scaled chronology is algebraically the unscaled physical defect
plus its `(p-1)` Euler memory, with no hypotheses on the chronology. -/
theorem amplitudeScaledPhysicalDefectLedger_eq_defect_add_memory
    (R : ℕ) (pre ps : List ℕ) :
    amplitudeScaledPhysicalDefectLedger R pre ps =
      amplitudePhysicalDefectLedger R pre ps +
        amplitudePhysicalMemoryLedger R pre ps := by
  induction ps generalizing pre with
  | nil =>
      simp [amplitudeScaledPhysicalDefectLedger,
        amplitudePhysicalDefectLedger, amplitudePhysicalMemoryLedger]
  | cons p ps ih =>
      simp only [amplitudeScaledPhysicalDefectLedger,
        amplitudePhysicalDefectLedger, amplitudePhysicalMemoryLedger]
      rw [ih (pre := pre ++ [p])]
      ring

/-- Unscaled physical defect ledger on the canonical complete descending
chronology. -/
def canonicalAmplitudePhysicalDefectLedger (R : ℕ) : ℂ :=
  amplitudePhysicalDefectLedger R []
    (squareRootCanonicalRoughDescendingPrimeSchedule R)

/-- Physical Euler-memory ledger on the same canonical chronology. -/
def canonicalAmplitudePhysicalMemoryLedger (R : ℕ) : ℂ :=
  amplitudePhysicalMemoryLedger R []
    (squareRootCanonicalRoughDescendingPrimeSchedule R)

/-- Canonical-schedule form of the exact AMP frontier.  No schedule witness is
left in the statement. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_add_memoryGap
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      canonicalAmplitudePhysicalDefectLedger R +
        (canonicalAmplitudePhysicalMemoryLedger R -
          lowOwnerReciprocalMertensColumn R) := by
  simpa [canonicalAmplitudePhysicalDefectLedger,
    canonicalAmplitudePhysicalMemoryLedger] using
    lowOwnerPhysicalAmplitudeRemainder_zero_eq_physicalDefectLedger_add_memoryGap
      R hR (squareRootCanonicalRoughDescendingPrimeSchedule R)
      (squareRootCanonicalRoughDescendingPrimeSchedule_complete R)

/-- Root-scale target for the unscaled physical Stokes/drop chronology. -/
def CanonicalAmplitudePhysicalDefectLedgerBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ, 56 ≤ R → LowerMertensCriticalEnvelope R K →
    ‖canonicalAmplitudePhysicalDefectLedger R‖ ^ 2 ≤
      C * (R : ℝ) ^ 2 * K

/-- Root-scale target for the normalization-memory discrepancy. -/
def CanonicalAmplitudePhysicalMemoryGapBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ, 56 ≤ R → LowerMertensCriticalEnvelope R K →
    ‖canonicalAmplitudePhysicalMemoryLedger R -
        lowOwnerReciprocalMertensColumn R‖ ^ 2 ≤
      C * (R : ℝ) ^ 2 * K

private theorem norm_add_sq_le_two_sum_sq_amp (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hnon : 0 ≤ ‖a + b‖ := norm_nonneg _
  have hsum : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Quantitative AMP closure reduction.  Separate root-scale bounds on the
unscaled physical defect and the memory mismatch give the required full
remainder bound. -/
theorem physicalAmplitudeRemainderBound_of_defect_and_memoryGap
    {CD CM : ℝ}
    (hD : CanonicalAmplitudePhysicalDefectLedgerBound CD)
    (hM : CanonicalAmplitudePhysicalMemoryGapBound CM) :
    LowOwnerPhysicalAmplitudeRemainderBound (2 * (CD + CM)) := by
  intro R K hR hK
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_add_memoryGap
    R hR]
  have htwo := norm_add_sq_le_two_sum_sq_amp
    (canonicalAmplitudePhysicalDefectLedger R)
    (canonicalAmplitudePhysicalMemoryLedger R -
      lowOwnerReciprocalMertensColumn R)
  have hDb := hD R K hR hK
  have hMb := hM R K hR hK
  calc
    ‖canonicalAmplitudePhysicalDefectLedger R +
        (canonicalAmplitudePhysicalMemoryLedger R -
          lowOwnerReciprocalMertensColumn R)‖ ^ 2 ≤
      2 * (‖canonicalAmplitudePhysicalDefectLedger R‖ ^ 2 +
        ‖canonicalAmplitudePhysicalMemoryLedger R -
          lowOwnerReciprocalMertensColumn R‖ ^ 2) := htwo
    _ ≤ 2 * ((CD * (R : ℝ) ^ 2 * K) +
      (CM * (R : ℝ) ^ 2 * K)) := by gcongr
    _ = (2 * (CD + CM)) * (R : ℝ) ^ 2 * K := by ring

/-- If the Euler-memory Fubini matches the reciprocal q^2 daughter column, the
entire AMP remainder is exactly the unscaled physical defect ledger on the
canonical chronology. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_of_memory_match
    (hmatch : AmplitudeEulerMemoryMatchesReciprocalQ2Daughters)
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      canonicalAmplitudePhysicalDefectLedger R := by
  have hsched := squareRootCanonicalRoughDescendingPrimeSchedule_complete R
  have hmem := hmatch R (squareRootCanonicalRoughDescendingPrimeSchedule R)
    hR hsched
  have hphys := correlationEulerMemoryLedger_eq_physicalMemoryLedger
    R (squareRootCanonicalRoughDescendingPrimeSchedule R) (by omega) hsched
  have hgap : canonicalAmplitudePhysicalMemoryLedger R -
      lowOwnerReciprocalMertensColumn R = 0 := by
    unfold canonicalAmplitudePhysicalMemoryLedger
    rw [← hphys, hmem]
    ring
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_add_memoryGap
    R hR, hgap]
  ring

/-- Consequently an exact memory match removes the factor-two split entirely:
a root-scale bound on the unscaled physical defect is already the full AMP
remainder bound. -/
theorem physicalAmplitudeRemainderBound_of_memory_match_and_defect
    (hmatch : AmplitudeEulerMemoryMatchesReciprocalQ2Daughters)
    {C : ℝ} (hD : CanonicalAmplitudePhysicalDefectLedgerBound C) :
    LowOwnerPhysicalAmplitudeRemainderBound C := by
  intro R K hR hK
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_of_memory_match
    hmatch R hR]
  exact hD R K hR hK

/-! ## Exact Abel pushforward gate

The zero-frequency AMP remainder is already the unscaled reciprocal Stokes
defect ledger plus the normalization-memory gap.  Therefore the proposed
collapse to the pure Stokes defect is not an additional algebraic consequence:
it is exactly the assertion that the chronological Euler memory equals the
reciprocal q^2 Mertens daughter column.

This statement is deliberately pointwise in R.  It lets finite diagnostics
falsify an over-strong pushforward without weakening the signed amplitude route.
-/

/-- Pointwise canonical-schedule form of the memory/q^2 match required by a
pure reciprocal-Stokes pushforward. -/
def CanonicalAmplitudeAbelMemoryMatchAt (R : ℕ) : Prop :=
  canonicalAmplitudePhysicalMemoryLedger R =
    lowOwnerReciprocalMertensColumn R

/-- **Exact Abel pushforward gate.**  At a fixed admissible root, the full
zero-frequency physical AMP remainder is the pure unscaled reciprocal Stokes
defect ledger if and only if the Euler-memory ledger is exactly the reciprocal
q^2 Mertens daughter column.

Thus a second reciprocal factor cannot be introduced merely by changing from
the prime-scaled raw chronology to the reciprocal Stokes coordinate; it has to
be supplied by this signed finite-Fubini identity (or by a different exact
pushforward that keeps the endpoint boundary attached). -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_iff_abelMemoryMatchAt
    (R : ℕ) (hR : 56 ≤ R) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
        canonicalAmplitudePhysicalDefectLedger R ↔
      CanonicalAmplitudeAbelMemoryMatchAt R := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_canonicalDefect_add_memoryGap
    R hR]
  unfold CanonicalAmplitudeAbelMemoryMatchAt
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]
    ring


end RHLean.Proof
