import Mathlib
import «research.DIRECT_SUM_COUPLED_RANGE_EXIT_COLLAPSE»
import RHLean.Proof.StableFarAdaptiveLedgerCollapse

/-!
# Global chronological collapse to the fresh-prime threshold ledger

The preceding range-exit module proves the pointwise statement needed at one
prime of the actual descending raw chronology: after every larger relevant
prime has already acted, the geometric range-exit contribution and the evolved
coefficient mismatch are both zero.  Hence the current raw boundary is exactly
the internal fresh-prime threshold term.

This file performs only the remaining iteration bookkeeping.  We record the
minimal stepwise hypothesis saying that every processed prefix is complete for
the current prime, prove that the whole range-exit ledger vanishes, and then
identify the complete fresh-prime threshold ledger with the canonical rough
critical correlation.

No norm, Cauchy inequality, q^2 energy estimate, PNT estimate, or RH-scale
hypothesis is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- The exact local hypothesis needed to iterate the #699 step theorem.
`pre` is the list of primes already processed and `todo` is the remaining
chronology.  At every current prime `p`, the processed prefix is complete for
all physically relevant larger primes. -/
def SquareRootCanonicalRoughStepwiseComplete (R : ℕ) :
    List ℕ → List ℕ → Prop
  | _pre, [] => True
  | pre, p :: ps =>
      p.Prime ∧
        SquareRootCanonicalRoughCompleteDescendingPrefix R p pre ∧
        SquareRootCanonicalRoughStepwiseComplete R (pre ++ [p]) ps

/-- Under a stepwise-complete descending chronology, the entire evolved
range-exit ledger vanishes.  This is just induction of the already compiled
one-step theorem; no estimate is introduced. -/
theorem directSumCoupledRangeExitLedger_eq_zero_of_stepwiseComplete
    (R : ℕ) (pre ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R pre ps) :
    directSumCoupledRangeExitLedger R ps
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) = 0 := by
  induction ps generalizing pre with
  | nil =>
      simp [directSumCoupledRangeExitLedger]
  | cons p ps ih =>
      rcases hstep with ⟨hp, hcomplete, htail⟩
      have hzero :=
        directSumCoupledRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
          R pre hR hp hcomplete
      dsimp at hzero
      simp only [directSumCoupledRangeExitLedger]
      rw [hzero, zero_add]
      have htailZero := ih (pre := pre ++ [p]) htail
      simpa [squareRootCanonicalRoughAdaptiveCarrier_append,
        squareRootCanonicalRoughAdaptiveRawCoefficient_append,
        squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveRawCoefficient] using htailZero

/-- Therefore the complete raw ledger is exactly the fresh-prime threshold
ledger on any stepwise-complete chronology. -/
theorem directSumCoupledFreshPrimeLedger_eq_rawLedger_of_stepwiseComplete
    (R : ℕ) (ps : List ℕ) (hR : 2 ≤ R)
    (hstep : SquareRootCanonicalRoughStepwiseComplete R [] ps) :
    directSumCoupledFreshPrimeLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) =
      squareRootCanonicalRoughAdaptiveRawLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) := by
  have hsplit :=
    squareRootCanonicalRoughAdaptiveRawLedger_eq_freshPrime_add_rangeExit
      R ps (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))
  have hzero :=
    directSumCoupledRangeExitLedger_eq_zero_of_stepwiseComplete
      R [] ps hR hstep
  simp [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] at hzero
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- A chronology carrying both the repository's global completeness predicate
and the literal prefix-completeness needed by the evolved #699 theorem. -/
def SquareRootCanonicalRoughFreshThresholdChronology
    (R : ℕ) (ps : List ℕ) : Prop :=
  SquareRootCanonicalRoughCompleteDescendingSchedule R ps ∧
    SquareRootCanonicalRoughStepwiseComplete R [] ps

/-- **Global fresh-prime normal form.**  On the actual complete descending
chronology, once the stepwise prefix condition is made explicit, the whole
canonical rough critical correlation is exactly the signed fresh-prime
threshold ledger.  There is no surviving range-exit or mismatch ledger. -/
theorem directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_chronology
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hchron : SquareRootCanonicalRoughFreshThresholdChronology R ps) :
    directSumCoupledFreshPrimeLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) =
      squareRootCanonicalRoughCorrelation R := by
  have hfresh :=
    directSumCoupledFreshPrimeLedger_eq_rawLedger_of_stepwiseComplete
      R ps (by omega) hchron.2
  have hraw :=
    adaptiveRawLedger_eq_roughCorrelation_of_completeSchedule
      R hR ps hchron.1
  exact hfresh.trans hraw

/-- Packet wrapper for the same exact identity. -/
theorem directSumCoupledFreshPrimePacket_eq_roughCorrelation_of_chronology
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hchron : SquareRootCanonicalRoughFreshThresholdChronology R ps) :
    directSumCoupledFreshPrimePacket R ps =
      squareRootCanonicalRoughCorrelation R := by
  unfold directSumCoupledFreshPrimePacket
  exact directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_chronology
    R hR ps hchron

end RHLean.Proof
