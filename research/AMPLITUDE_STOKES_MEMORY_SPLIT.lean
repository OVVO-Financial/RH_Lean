import Mathlib
import «research.LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE»
import RHLean.Proof.PostRootPartnerEulerMemory

/-!
# Exact Stokes / Euler-memory split of the AMP remainder

The raw adaptive ledger has a canonical intermediate state at every fresh-prime
step: the reciprocal Euler next state.  Insert that state algebraically between
the raw current state and the raw next state:

  RawCurrent - RawNext
    = (RawCurrent - EulerNext) + (EulerNext - RawNext).

The first bracket is the reciprocal Stokes drop.  The second is the Euler-memory
term.  Because the raw one-step theorem identifies `RawCurrent - RawNext` with
the signed physical boundary plus coefficient mismatch, the same decomposition
iterates along the entire raw chronology before any norm.

On a complete descending schedule the raw ledger is the canonical rough
correlation, so

  Corr_R = DropLedger_R + MemoryLedger_R.

Combining this with #715 gives the exact zero-frequency AMP frontier

  Remainder_R
    = DropLedger_R + (MemoryLedger_R - ReciprocalQ2DaughterColumn_R).

Thus the proof has two precise remaining tasks: identify the memory ledger with
the reciprocal q^2 daughter column, and bound the reciprocal-drop ledger on its
literal physical owner graph.  No estimate is assumed in this file.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Cofactor-weighted reciprocal coefficient used to compare the raw and Euler
coordinates at one evolved step. -/
def amplitudeEulerCoordinate (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) * a n

/-- Reciprocal Stokes drop between the raw current state and reciprocal Euler
next state. -/
def amplitudeReciprocalDropStep
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  squareRootCanonicalRoughAdaptiveRawWeightedMass R U a -
    squareRootCanonicalRoughAdaptiveWeightedMass R
      (squareRootCanonicalRoughAdaptiveNextCarrier p U)
      (squareRootCanonicalRoughAdaptiveNextCoefficient p U
        (amplitudeEulerCoordinate a))

/-- Euler-memory term between reciprocal Euler next state and raw zero-factor
next state. -/
def amplitudeEulerMemoryStep
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  squareRootCanonicalRoughAdaptiveWeightedMass R
      (squareRootCanonicalRoughAdaptiveNextCarrier p U)
      (squareRootCanonicalRoughAdaptiveNextCoefficient p U
        (amplitudeEulerCoordinate a)) -
    squareRootCanonicalRoughAdaptiveRawWeightedMass R
      (squareRootCanonicalRoughAdaptiveNextCarrier p U)
      (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- One raw wall-plus-mismatch step is exactly Stokes drop plus Euler memory. -/
theorem rawBoundary_add_mismatch_eq_reciprocalDrop_add_eulerMemory
    (R : ℕ) {p : ℕ} (U : Finset ℕ) (a : ℕ → ℂ)
    (hR : 2 ≤ R) (hp : p.Prime) :
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a +
        squareRootCanonicalRoughAdaptiveRawMismatchMass R p U a =
      amplitudeReciprocalDropStep R p U a +
        amplitudeEulerMemoryStep R p U a := by
  have hraw :=
    adaptiveRawWeightedMass_eq_next_add_boundary_add_mismatch
      R U a hR hp
  unfold amplitudeReciprocalDropStep amplitudeEulerMemoryStep
  ring_nf at hraw ⊢
  exact hraw.symm

/-- Cumulative reciprocal Stokes drops along the actual raw chronology. -/
def amplitudeReciprocalDropLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      amplitudeReciprocalDropStep R p U a +
        amplitudeReciprocalDropLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- Cumulative Euler memory along the same raw chronology. -/
def amplitudeEulerMemoryLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      amplitudeEulerMemoryStep R p U a +
        amplitudeEulerMemoryLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)

/-- **Exact many-prime Stokes-memory split.**  The raw signed ledger equals the
sum of the reciprocal-drop ledger and the Euler-memory ledger before any norm. -/
theorem adaptiveRawLedger_eq_reciprocalDropLedger_add_eulerMemoryLedger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    squareRootCanonicalRoughAdaptiveRawLedger R ps U a =
      amplitudeReciprocalDropLedger R ps U a +
        amplitudeEulerMemoryLedger R ps U a := by
  induction ps generalizing U a with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveRawLedger,
        amplitudeReciprocalDropLedger, amplitudeEulerMemoryLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hone :=
        rawBoundary_add_mismatch_eq_reciprocalDrop_add_eulerMemory
          R U a hR hp
      have htail := ih
        (U := squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (a := squareRootCanonicalRoughAdaptiveRawNextCoefficient p U a)
        hps
      simp only [squareRootCanonicalRoughAdaptiveRawLedger,
        amplitudeReciprocalDropLedger, amplitudeEulerMemoryLedger]
      rw [hone, htail]
      ring

/-- Unit-coefficient reciprocal-drop ledger on a chosen schedule. -/
def correlationReciprocalDropLedger (R : ℕ) (ps : List ℕ) : ℂ :=
  amplitudeReciprocalDropLedger R ps
    (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))

/-- Unit-coefficient Euler-memory ledger on the same schedule. -/
def correlationEulerMemoryLedger (R : ℕ) (ps : List ℕ) : ℂ :=
  amplitudeEulerMemoryLedger R ps
    (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))

/-- On any complete descending schedule, the canonical rough correlation is
exactly reciprocal Stokes drops plus Euler memory. -/
theorem correlation_eq_reciprocalDropLedger_add_eulerMemoryLedger
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    squareRootCanonicalRoughCorrelation R =
      correlationReciprocalDropLedger R ps +
        correlationEulerMemoryLedger R ps := by
  have hsplit :=
    adaptiveRawLedger_eq_reciprocalDropLedger_add_eulerMemoryLedger
      R (by omega) ps (Finset.Icc 1 (squareRootEndpoint R))
      (fun _ => (1 : ℂ)) hsched.1
  have hcorr :=
    adaptiveRawCorrelationLedger_eq_correlation_of_completeSchedule
      R hR ps hsched
  unfold adaptiveRawCorrelationLedger at hcorr
  unfold correlationReciprocalDropLedger correlationEulerMemoryLedger
  rw [← hcorr]
  exact hsplit

/-- **Exact zero-frequency AMP frontier.**  The full physical remainder is the
reciprocal Stokes-drop ledger plus the discrepancy between Euler memory and the
reciprocal q^2 daughter column. -/
theorem lowOwnerPhysicalAmplitudeRemainder_zero_eq_dropLedger_add_memoryGap
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      correlationReciprocalDropLedger R ps +
        (correlationEulerMemoryLedger R ps -
          lowOwnerReciprocalMertensColumn R) := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_correlation_sub_reciprocalColumn
      R hR,
    correlation_eq_reciprocalDropLedger_add_eulerMemoryLedger R hR ps hsched]
  ring

/-- Exact statement of the remaining memory identification.  It is intentionally
separate from the quantitative drop estimate. -/
def AmplitudeEulerMemoryMatchesReciprocalQ2Daughters : Prop :=
  ∀ R : ℕ, ∀ ps : List ℕ,
    56 ≤ R → SquareRootCanonicalRoughCompleteDescendingSchedule R ps →
      correlationEulerMemoryLedger R ps = lowOwnerReciprocalMertensColumn R

/-- Once the memory ledger is identified with the reciprocal q^2 daughters, the
entire AMP remainder is exactly the reciprocal Stokes-drop ledger. -/
theorem physicalAmplitudeRemainder_eq_reciprocalDropLedger_of_memory_match
    (hmatch : AmplitudeEulerMemoryMatchesReciprocalQ2Daughters)
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowOwnerPhysicalAmplitudeRemainder R 0 =
      correlationReciprocalDropLedger R ps := by
  rw [lowOwnerPhysicalAmplitudeRemainder_zero_eq_dropLedger_add_memoryGap
      R hR ps hsched,
    hmatch R ps hR hsched]
  ring

end RHLean.Proof
