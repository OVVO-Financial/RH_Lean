import Mathlib
import «research.DIRECT_SUM_COUPLED_RANGE_EXIT_COLLAPSE»
import RHLean.Proof.StableFarAdaptiveLedgerCollapse

/-!
# Global collapse of the evolved range-exit ledger

The stepwise theorem says that on the actual descending chronology every
non-threshold range-exit contribution is already zero.  This file packages that
local statement over a complete descending schedule while keeping track of the
literal processed prefix.  The result identifies the surviving fresh-prime
threshold ledger with the canonical rough correlation exactly, before norms.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- If a complete-schedule witness for a larger prime `q` is compared with a
concrete occurrence of a smaller current prime `p`, then that witnessed `q`
must already lie in the processed prefix. -/
private theorem larger_witness_splits_before_current
    {p q : ℕ} (qs post pre tail : List ℕ)
    (hsplit : qs ++ p :: post = pre ++ q :: tail)
    (hpq : p < q)
    (hlarger : ∀ r ∈ pre, q < r) :
    ∃ pre' post',
      qs = pre' ++ q :: post' ∧
        (∀ r ∈ pre', q < r) := by
  induction qs generalizing pre post tail with
  | nil =>
      cases pre with
      | nil =>
          have hpqeq : p = q := (List.cons.inj hsplit).1
          omega
      | cons r rs =>
          have hhead : p = r := (List.cons.inj hsplit).1
          have hr : q < r := hlarger r (by simp)
          omega
  | cons r rs ih =>
      cases pre with
      | nil =>
          have hrq : r = q := (List.cons.inj hsplit).1
          subst r
          refine ⟨[], rs, ?_, ?_⟩
          · simp
          · intro x hx
            simp at hx
      | cons s pre =>
          have hhead : r = s := (List.cons.inj hsplit).1
          have htail : rs ++ p :: post = pre ++ q :: tail :=
            (List.cons.inj hsplit).2
          have hlargerTail : ∀ x ∈ pre, q < x := by
            intro x hx
            exact hlarger x (by simp [hx])
          rcases ih (pre := pre) (post := post) (tail := tail)
              htail hpq hlargerTail with
            ⟨pre', post', hrs, hgt⟩
          refine ⟨r :: pre', post', ?_, ?_⟩
          · simp [hrs]
          · intro x hx
            simp at hx
            rcases hx with rfl | hx
            · rw [hhead]
              exact hlarger s (by simp)
            · exact hgt x hx

/-- Any literal processed prefix of a complete descending schedule is complete
above its current prime.  This is the bridge needed to iterate the stepwise
range-exit cancellation on the actual recursive ledger state. -/
theorem completeDescendingPrefix_of_completeSchedule_split
    (R : ℕ) (qs post : List ℕ) {p : ℕ}
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule
      R (qs ++ p :: post)) :
    SquareRootCanonicalRoughCompleteDescendingPrefix R p qs := by
  constructor
  · intro r hr
    apply hsched.1 r
    simp [hr]
  · intro q hq hpq hqUpper
    rcases hsched.2 q hq hqUpper with
      ⟨pre, tail, hsplit, hprePrime, hpreLarger⟩
    rcases larger_witness_splits_before_current
        qs post pre tail hsplit hpq hpreLarger with
      ⟨pre', post', hqs, hgt⟩
    refine ⟨pre', post', hqs, ?_, hgt⟩
    intro r hr
    apply hsched.1 r
    have hrqs : r ∈ qs := by
      rw [hqs]
      simp [hr]
    simp [hrqs]

/-- Globalized form of the stepwise result.  Starting from any already-processed
prefix of the same complete schedule, the remaining range-exit ledger is zero. -/
theorem directSumCoupledRangeExitLedger_eq_zero_from_completeSchedule_split
    (R : ℕ) (hR : 2 ≤ R) (pre rest : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule
      R (pre ++ rest)) :
    directSumCoupledRangeExitLedger R rest
        (squareRootCanonicalRoughAdaptiveCarrier pre
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient pre
          (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))) = 0 := by
  induction rest generalizing pre with
  | nil =>
      simp [directSumCoupledRangeExitLedger]
  | cons p ps ih =>
      have hp : p.Prime := hsched.1 p (by simp)
      have hprefix :=
        completeDescendingPrefix_of_completeSchedule_split
          R pre ps hsched
      have hstep :=
        directSumCoupledRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
          R pre hR hp hprefix
      dsimp at hstep
      have hschedTail :
          SquareRootCanonicalRoughCompleteDescendingSchedule
            R ((pre ++ [p]) ++ ps) := by
        simpa [List.append_assoc] using hsched
      have htail := ih (pre := pre ++ [p]) hschedTail
      rw [squareRootCanonicalRoughAdaptiveCarrier_append,
        squareRootCanonicalRoughAdaptiveRawCoefficient_append] at htail
      simp only [squareRootCanonicalRoughAdaptiveCarrier,
        squareRootCanonicalRoughAdaptiveRawCoefficient] at htail
      simp only [directSumCoupledRangeExitLedger]
      rw [hstep]
      simp only [zero_add]
      exact htail

/-- On every complete descending schedule the full chronological range-exit and
mismatch ledger is identically zero. -/
theorem directSumCoupledRangeExitLedger_eq_zero_of_completeSchedule
    (R : ℕ) (hR : 2 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledRangeExitLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) = 0 := by
  have h :=
    directSumCoupledRangeExitLedger_eq_zero_from_completeSchedule_split
      R hR [] ps (by simpa using hsched)
  simpa [squareRootCanonicalRoughAdaptiveCarrier,
    squareRootCanonicalRoughAdaptiveRawCoefficient] using h

/-- **Fresh-prime normal form.**  After the chronological range-exit collapse,
the surviving fresh-prime threshold ledger is exactly the canonical rough
critical correlation.  No terminal, birth, mismatch, or final-state term
remains. -/
theorem directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledFreshPrimeLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) =
      squareRootCanonicalRoughCorrelation R := by
  have hsplit :=
    squareRootCanonicalRoughAdaptiveRawLedger_eq_freshPrime_add_rangeExit
      R ps (Finset.Icc 1 (squareRootEndpoint R)) (fun _ => (1 : ℂ))
  have hraw :=
    adaptiveRawLedger_eq_roughCorrelation_of_completeSchedule
      R hR ps hsched
  have hexit :=
    directSumCoupledRangeExitLedger_eq_zero_of_completeSchedule
      R (by omega) ps hsched
  rw [hraw, hexit, add_zero] at hsplit
  exact hsplit.symm

/-- Packet-level spelling of the same normal form. -/
theorem directSumCoupledFreshPrimePacket_eq_roughCorrelation_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R) (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    directSumCoupledFreshPrimePacket R ps =
      squareRootCanonicalRoughCorrelation R := by
  unfold directSumCoupledFreshPrimePacket
  exact directSumCoupledFreshPrimeLedger_eq_roughCorrelation_of_completeSchedule
    R hR ps hsched

end RHLean.Proof
