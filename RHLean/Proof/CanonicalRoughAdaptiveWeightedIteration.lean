import Mathlib
import RHLean.Proof.CanonicalRoughAdaptiveWeightedEulerCompression

/-!
# Iterated weighted adaptive Euler compression

The one-prime weighted adaptive identity keeps the genuine Euler factor on every
coherent parent/child pair and records the exact coefficient mismatch when two
endpoints inherited different larger-prime histories.  This module iterates that
identity without taking a norm.

The result is a literal chronological formula:

```text
initial weighted mass
  = final adaptive weighted mass
    + signed weighted physical defects
    + signed coefficient mismatches.
```

Thus a descending-prime proof may attack the two signed ledgers directly.  No
survivor is frozen and no missing commuting-square corner is silently assigned
an Euler factor.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- Coefficient field remaining after a chronological adaptive prime list. -/
def squareRootCanonicalRoughAdaptiveCoefficient :
    List ℕ → Finset ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | [], _U, a => a
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveCoefficient ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a)

/-- Signed correction created at one weighted adaptive step. -/
def squareRootCanonicalRoughAdaptiveWeightedStepCorrection
    (R p : ℕ) (U : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
    squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a

/-- Cumulative signed weighted corrections along a chronological adaptive run. -/
def squareRootCanonicalRoughAdaptiveWeightedLedger
    (R : ℕ) : List ℕ → Finset ℕ → (ℕ → ℂ) → ℂ
  | [], _U, _a => 0
  | p :: ps, U, a =>
      squareRootCanonicalRoughAdaptiveWeightedStepCorrection R p U a +
        squareRootCanonicalRoughAdaptiveWeightedLedger R ps
          (squareRootCanonicalRoughAdaptiveNextCarrier p U)
          (squareRootCanonicalRoughAdaptiveNextCoefficient p U a)

/-- Split the cumulative ledger into its current physical-defect and mismatch
atoms followed by the later adaptive run. -/
@[simp] theorem squareRootCanonicalRoughAdaptiveWeightedLedger_cons
    (R p : ℕ) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ) :
    squareRootCanonicalRoughAdaptiveWeightedLedger R (p :: ps) U a =
      squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
      squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps
        (squareRootCanonicalRoughAdaptiveNextCarrier p U)
        (squareRootCanonicalRoughAdaptiveNextCoefficient p U a) := by
  simp [squareRootCanonicalRoughAdaptiveWeightedLedger,
    squareRootCanonicalRoughAdaptiveWeightedStepCorrection]

/-- **Exact iterated weighted adaptive descent.**  Every requested prime acts on
exactly the carrier and coefficient field left by the earlier primes.  The only
booked correction terms are the intact signed physical defect and the intact
signed coefficient mismatch. -/
theorem adaptiveWeightedMass_eq_adaptiveCarrier_add_weightedLedger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ) (a : ℕ → ℂ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    squareRootCanonicalRoughAdaptiveWeightedMass R U a =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveCoefficient ps U a) +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps U a := by
  induction ps generalizing U a with
  | nil =>
      simp [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveCoefficient,
        squareRootCanonicalRoughAdaptiveWeightedLedger]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hps : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      let U' := squareRootCanonicalRoughAdaptiveNextCarrier p U
      let a' := squareRootCanonicalRoughAdaptiveNextCoefficient p U a
      have hone :=
        adaptiveWeightedMass_eq_next_add_physicalDefect_add_mismatch
          R U a hR hp
      have htail := ih (U := U') (a := a') hps
      calc
        squareRootCanonicalRoughAdaptiveWeightedMass R U a =
            squareRootCanonicalRoughAdaptiveWeightedMass R U' a' +
              squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
              squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
          simpa [U', a'] using hone
        _ = (squareRootCanonicalRoughAdaptiveWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier ps U')
              (squareRootCanonicalRoughAdaptiveCoefficient ps U' a') +
              squareRootCanonicalRoughAdaptiveWeightedLedger R ps U' a') +
              squareRootCanonicalRoughAdaptiveWeightedPhysicalDefectMass R p U a +
              squareRootCanonicalRoughAdaptiveCoefficientMismatchMass R p U a := by
          rw [htail]
        _ = squareRootCanonicalRoughAdaptiveWeightedMass R
              (squareRootCanonicalRoughAdaptiveCarrier (p :: ps) U)
              (squareRootCanonicalRoughAdaptiveCoefficient (p :: ps) U a) +
              squareRootCanonicalRoughAdaptiveWeightedLedger R (p :: ps) U a := by
          simp only [squareRootCanonicalRoughAdaptiveCarrier,
            squareRootCanonicalRoughAdaptiveCoefficient,
            squareRootCanonicalRoughAdaptiveWeightedLedger,
            squareRootCanonicalRoughAdaptiveWeightedStepCorrection]
          dsimp [U', a']
          ring

/-- Unit initial coefficients specialize the exact iteration to the native
uncentered reciprocal correlation on the chosen carrier. -/
theorem sum_correlationReciprocal_eq_adaptiveWeightedUnitCarrier_add_ledger
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ) (U : Finset ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) :
    (∑ n ∈ U, squareRootCanonicalRoughCorrelationReciprocalSummand R n) =
      squareRootCanonicalRoughAdaptiveWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps U)
        (squareRootCanonicalRoughAdaptiveCoefficient ps U (fun _ => (1 : ℂ))) +
      squareRootCanonicalRoughAdaptiveWeightedLedger R ps U (fun _ => (1 : ℂ)) := by
  have h := adaptiveWeightedMass_eq_adaptiveCarrier_add_weightedLedger
    R hR ps U (fun _ => (1 : ℂ)) hprime
  simpa [squareRootCanonicalRoughAdaptiveWeightedMass] using h

end RHLean.Proof
