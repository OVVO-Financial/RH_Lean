import Mathlib
import RHLean.Proof.PostRootPartnerEulerMemory
import RHLean.Proof.FrozenTopFarAdaptiveRawBridge
import RHLean.Proof.TerminalMertensReduction

/-!
# Complete descending schedules leave no final raw mass

The adaptive raw representation of the frozen/top/far residual has two pieces:
a final raw mass and the chronological signed boundary/mismatch ledger.  The
final mass is not intrinsic.  If the prime schedule is complete and descending,
every cofactor with nonzero rough response has an actual prime partner `q`.
That partner occurs while all larger coordinates have already been processed;
the cofactor and its `q`-child are therefore still present, so the cofactor is a
literal `q`-parent and its zero-factor coefficient is killed permanently.

Consequently the final raw mass is exactly zero.  The frozen/top/far residual
is then the signed chronological ledger plus the already root-scale correction.
No norm or analytic estimate is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- A schedule contains every prime that could occur below the square endpoint,
and each such prime occurs after a prefix consisting only of strictly larger
prime coordinates.  This is exactly the structural property needed by the
zero-factor parent kill; no quantitative statement is included. -/
def SquareRootCanonicalRoughCompleteDescendingSchedule
    (R : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime) ∧
    ∀ q : ℕ, q.Prime → q ≤ squareRootEndpoint R →
      ∃ pre post,
        ps = pre ++ q :: post ∧
          (∀ r ∈ pre, r.Prime) ∧
          (∀ r ∈ pre, q < r)

/-- Every cofactor carrying nonzero raw rough correlation is killed somewhere
in a complete descending schedule. -/
theorem rawCoefficient_eq_zero_of_nonzero_rawCorrelation_completeSchedule
    (R : ℕ) (ps : List ℕ)
    (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps)
    {n : ℕ}
    (hnFinal : n ∈ squareRootCanonicalRoughAdaptiveCarrier ps
      (Finset.Icc 1 (squareRootEndpoint R)))
    (hraw : squareRootCanonicalRoughRawCorrelationSummand R n ≠ 0) :
    squareRootCanonicalRoughAdaptiveRawCoefficient ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) n = 0 := by
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  have hnU0 : n ∈ U0 :=
    squareRootCanonicalRoughAdaptiveCarrier_subset ps U0 hnFinal
  have hnRange := Finset.mem_Icc.mp hnU0
  have hnpos : 0 < n := by omega

  have hresponse : squareRootCanonicalRoughCofactorResponse R n ≠ 0 := by
    intro hzero
    apply hraw
    simp [squareRootCanonicalRoughRawCorrelationSummand, hzero]

  have hpartners : (squareRootCanonicalRoughPrimePartnerSet R n).Nonempty := by
    by_contra hempty
    have hset : squareRootCanonicalRoughPrimePartnerSet R n = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hresponse
    rw [squareRootCanonicalRoughCofactorResponse_eq_primePartnerCount R n hR,
      squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card R n, hset]
    simp

  rcases hpartners with ⟨q, hqSet⟩
  rcases (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hnpos).mp hqSet with
    ⟨hqPrime, hrough, _hroot, hupper⟩
  have hqleProd : q ≤ n * q := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right q hnpos
  have hqUpper : q ≤ squareRootEndpoint R := hqleProd.trans hupper
  rcases hsched.2 q hqPrime hqUpper with
    ⟨pre, post, hsplit, hprePrime, hpreLarger⟩

  have hnPre : n ∈ squareRootCanonicalRoughAdaptiveCarrier pre U0 := by
    apply mem_adaptiveCarrier_of_all_larger_primes pre hnU0 hprePrime
    intro r hr
    exact hrough.trans (hpreLarger r hr)

  have hnqPos : 0 < n * q := Nat.mul_pos hnpos hqPrime.pos
  have hnqU0 : n * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnqPos), hupper⟩
  have hlpfNQ : canonicalLargestPrimeFactor (n * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hnpos hqPrime hrough
  have hnqPre : n * q ∈ squareRootCanonicalRoughAdaptiveCarrier pre U0 := by
    apply mem_adaptiveCarrier_of_all_larger_primes pre hnqU0 hprePrime
    intro r hr
    rw [hlpfNQ]
    exact hpreLarger r hr

  have hnParent :
      n ∈ squareRootCanonicalRoughFreshPrimeParentsOn q
        (squareRootCanonicalRoughAdaptiveCarrier pre U0) := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hnPre, hnpos, hrough, hnqPre⟩

  rw [hsplit]
  exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
    pre post U0 (fun _ => (1 : ℂ)) hnParent

/-- **Complete descending schedules have zero final raw mass.** -/
theorem adaptiveRawFinalMass_eq_zero_of_completeDescendingSchedule
    (R : ℕ) (ps : List ℕ)
    (hR : 2 ≤ R)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    squareRootCanonicalRoughAdaptiveRawWeightedMass R
        (squareRootCanonicalRoughAdaptiveCarrier ps
          (Finset.Icc 1 (squareRootEndpoint R)))
        (squareRootCanonicalRoughAdaptiveRawCoefficient ps
          (Finset.Icc 1 (squareRootEndpoint R))
          (fun _ => (1 : ℂ))) = 0 := by
  unfold squareRootCanonicalRoughAdaptiveRawWeightedMass
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hraw : squareRootCanonicalRoughRawCorrelationSummand R n = 0
  · simp [hraw]
  · have hcoef :=
      rawCoefficient_eq_zero_of_nonzero_rawCorrelation_completeSchedule
        R ps hR hsched hn hraw
    rw [hcoef]
    simp

/-- On a complete descending schedule the frozen/top/far residual has no final
adaptive raw remainder: it is exactly the signed chronological ledger plus the
explicit root-scale correction. -/
theorem lowWheelFrozenTopFarResidual_eq_rawLedger_add_rootCorrection_of_completeSchedule
    (R : ℕ) (hR : 56 ≤ R)
    (ps : List ℕ)
    (hsched : SquareRootCanonicalRoughCompleteDescendingSchedule R ps) :
    lowWheelFrozenTopFarResidual R =
      squareRootCanonicalRoughAdaptiveRawLedger R ps
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) +
      frozenTopFarRoughRootCorrection R := by
  have hprime := hsched.1
  have hbridge :=
    lowWheelFrozenTopFarResidual_eq_adaptiveRawFinal_add_ledger_add_rootCorrection
      R hR ps hprime
  have hfinal :=
    adaptiveRawFinalMass_eq_zero_of_completeDescendingSchedule
      R ps (by omega) hsched
  rw [hfinal, zero_add] at hbridge
  exact hbridge

end RHLean.Proof
