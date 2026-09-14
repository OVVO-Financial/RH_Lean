import Mathlib
import «research.DIRECT_SUM_COUPLED_RANGE_EXIT_COLLAPSE»
import RHLean.Proof.StableFarAdaptiveLedgerCollapse

/-!
# Global chronological collapse to the fresh-prime threshold ledger

The preceding range-exit module proves the pointwise statement needed at one
prime of the actual descending raw chronology: after every larger relevant
prime has already acted, the geometric range-exit contribution and the evolved
coefficient mismatch are both zero. Hence the current raw boundary is exactly
the internal fresh-prime threshold term.

This file performs the remaining finite iteration bookkeeping. The repository's
existing complete-schedule predicate already implies that every literal
processed prefix is complete for the current prime: if a larger relevant prime
were scheduled after the current one, the current smaller prime would occur in
that larger prime's certified prefix, contradicting strict largeness there.
After compiling that list-order fact, the whole range-exit ledger vanishes and
the fresh-prime threshold ledger is exactly the canonical rough critical
correlation.

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
chronology. At every current prime `p`, the processed prefix is complete for
all physically relevant larger primes. -/
def SquareRootCanonicalRoughStepwiseComplete (R : ℕ) :
    List ℕ → List ℕ → Prop
  | _pre, [] => True
  | pre, p :: ps =>
      p.Prime ∧
        SquareRootCanonicalRoughCompleteDescendingPrefix R p pre ∧
        SquareRootCanonicalRoughStepwiseComplete R (pre ++ [p]) ps

/-- Elementary order lemma for two marked positions in the same list. If the
marks are distinct, one marked occurrence lies in the prefix of the other. -/
private theorem list_two_marked_splits_order
    {pre post pre' post' : List ℕ} {p q : ℕ}
    (hpq : p ≠ q)
    (h : pre ++ p :: post = pre' ++ q :: post') :
    (∃ mid, pre = pre' ++ q :: mid) ∨
      (∃ mid, pre' = pre ++ p :: mid) := by
  induction pre generalizing pre' with
  | nil =>
      cases pre' with
      | nil =>
          simp only [List.nil_append] at h
          have hpq' : p = q := (List.cons.inj h).1
          exact (hpq hpq').elim
      | cons a pre' =>
          simp only [List.nil_append, List.cons_append] at h
          have hpa : p = a := (List.cons.inj h).1
          right
          refine ⟨pre', ?_⟩
          simp [hpa]
  | cons a pre ih =>
      cases pre' with
      | nil =>
          simp only [List.cons_append, List.nil_append] at h
          have haq : a = q := (List.cons.inj h).1
          left
          refine ⟨pre, ?_⟩
          simp [haq]
      | cons b pre' =>
          simp only [List.cons_append] at h
          have hab : a = b := (List.cons.inj h).1
          have htail : pre ++ p :: post = pre' ++ q :: post' :=
            (List.cons.inj h).2
          rcases ih (pre' := pre') htail with ⟨mid, hm⟩ | ⟨mid, hm⟩
          · left
            refine ⟨mid, ?_⟩
            simp [hab, hm]
          · right
            refine ⟨mid, ?_⟩
            simp [hab, hm]

/-- Any literal prefix before a current prime in a complete descending schedule
is already a complete descending prefix in the sense required by the evolved
#699 theorem. -/
theorem squareRootCanonicalRoughCompleteDescendingPrefix_of_schedule_split
    (R : ℕ) (ps pre post : List ℕ) (p : ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps)
    (hsplit : ps = pre ++ p :: post) :
    SquareRootCanonicalRoughCompleteDescendingPrefix R p pre := by
  constructor
  · intro r hr
    apply hsched.1 r
    rw [hsplit]
    simp [hr]
  · intro q hq hpq hqUpper
    rcases hsched.2 q hq hqUpper with
      ⟨qpre, qpost, hqsplit, hqprePrime, hqpreLarger⟩
    have heq : pre ++ p :: post = qpre ++ q :: qpost := by
      calc
        pre ++ p :: post = ps := hsplit.symm
        _ = qpre ++ q :: qpost := hqsplit
    have hpqne : p ≠ q := Nat.ne_of_lt hpq
    rcases list_two_marked_splits_order hpqne heq with
      ⟨mid, hbefore⟩ | ⟨mid, hafter⟩
    · exact ⟨qpre, mid, hbefore, hqprePrime, hqpreLarger⟩
    · have hpMem : p ∈ qpre := by
        rw [hafter]
        simp
      have hqp : q < p := hqpreLarger p hpMem
      omega

/-- The repository's global complete-schedule predicate therefore supplies the
stepwise prefix hypothesis automatically; no stronger schedule assumption is
needed. -/
theorem squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
    (R : ℕ) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    SquareRootCanonicalRoughStepwiseComplete R [] ps := by
  have aux : ∀ (pre todo : List ℕ),
      ps = pre ++ todo →
        SquareRootCanonicalRoughStepwiseComplete R pre todo := by
    intro pre todo hsplit
    induction todo generalizing pre with
    | nil =>
        simp [SquareRootCanonicalRoughStepwiseComplete]
    | cons p tail ih =>
        have hfull : ps = pre ++ p :: tail := by simpa using hsplit
        have hp : p.Prime := by
          apply hsched.1 p
          rw [hfull]
          simp
        have hprefix :=
          squareRootCanonicalRoughCompleteDescendingPrefix_of_schedule_split
            R ps pre tail p hsched hfull
        have htail :
            SquareRootCanonicalRoughStepwiseComplete R (pre ++ [p]) tail := by
          apply ih (pre := pre ++ [p])
          simpa [List.append_assoc] using hfull
        exact ⟨hp, hprefix, htail⟩
  exact aux [] ps (by simp)

/-- Under a stepwise-complete descending chronology, the entire evolved
range-exit ledger vanishes. This is just induction of the already compiled
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

/-- The cumulative range-exit ledger vanishes on every repository-complete
descending schedule. -/
theorem directSumCoupledRangeExitLedger_eq_zero_of_completeDescendingSchedule
    (R : ℕ) (ps : List ℕ) (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledRangeExitLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) = 0 := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  have hzero :=
    directSumCoupledRangeExitLedger_eq_zero_of_stepwiseComplete
      R [] ps hR hstep
  simpa [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] using hzero

/-- **Global fresh-prime normal form.** On every complete descending schedule,
the whole canonical rough critical correlation is exactly the signed
fresh-prime threshold ledger. There is no surviving range-exit, birth, top
escape, coefficient mismatch, or final adaptive state. -/
theorem directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledFreshPrimeLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ)) =
      squareRootCanonicalRoughCorrelation R := by
  have hstep :=
    squareRootCanonicalRoughStepwiseComplete_of_completeDescendingSchedule
      R ps hsched
  have hfresh :=
    directSumCoupledFreshPrimeLedger_eq_rawLedger_of_stepwiseComplete
      R ps (by omega) hstep
  have hraw :=
    adaptiveRawLedger_eq_roughCorrelation_of_completeSchedule
      R hR ps hsched
  exact hfresh.trans hraw

/-- Packet wrapper for the same exact identity. -/
theorem directSumCoupledFreshPrimePacket_eq_roughCorrelation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledFreshPrimePacket R ps =
      squareRootCanonicalRoughCorrelation R := by
  unfold directSumCoupledFreshPrimePacket
  exact directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_completeSchedule
    R hR ps hsched

end RHLean.Proof
