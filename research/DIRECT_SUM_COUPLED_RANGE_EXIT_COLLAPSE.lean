import Mathlib
import «research.DIRECT_SUM_COUPLED_FRESH_PRIME_RANGE_EXIT»

/-!
# Coupled direct-sum packet: chronological range-exit collapse

The fresh-prime/range-exit split keeps three kinds of non-threshold terms:
terminal top escape, lower-root birth, and inherited-coefficient mismatch.
On the literal descending raw chronology all three vanish at the current step.

For either a top escape or a birth there is a larger prime `q > p` with
`c*q <= X_R`.  Completeness of the already-processed descending prefix forces
that `q` to have acted earlier, while both `c` and `c*q` were still present.
Thus the raw zero-factor update at `q` already killed the coefficient of `c`.
The mismatch term is already known to vanish on the same complete descending
prefix.  Hence the whole evolved range-exit step is identically zero; this is
an exact chronological statement, not a norm estimate.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic
open CanonicalRoughPrimeAdditionDescent

attribute [local instance] Classical.propDecidable

/-- A current cofactor whose response has any larger prime partner has already
had its raw coefficient killed when that larger prime was processed. -/
theorem evolvedRawCoefficient_eq_zero_of_larger_partner_of_completeDescendingPrefix
    {R c p q : ℕ} (qs : List ℕ)
    (hc : 0 < c) (_hp : p.Prime) (hq : q.Prime)
    (hrough : canonicalLargestPrimeFactor c < p)
    (hpq : p < q)
    (hcqUpper : c * q ≤ squareRootEndpoint R)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    squareRootCanonicalRoughAdaptiveRawCoefficient qs
        (Finset.Icc 1 (squareRootEndpoint R))
        (fun _ => (1 : ℂ)) c = 0 := by
  have hqUpper : q ≤ squareRootEndpoint R := by
    have hq_le_cq : q ≤ c * q := by
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right q hc
    exact hq_le_cq.trans hcqUpper
  rcases hcomplete.2 q hq hpq hqUpper with
    ⟨pre, post, hsplit, hprePrime, hpreLarger⟩
  let U0 : Finset ℕ := Finset.Icc 1 (squareRootEndpoint R)
  let V : Finset ℕ := squareRootCanonicalRoughAdaptiveCarrier pre U0
  have hroughQ : canonicalLargestPrimeFactor c < q := hrough.trans hpq
  have hc_le_cq : c ≤ c * q := by
    simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right c hq.pos
  have hcU0 : c ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, hc_le_cq.trans hcqUpper⟩
  have hcqPos : 0 < c * q := Nat.mul_pos hc hq.pos
  have hcqU0 : c * q ∈ U0 := by
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcqPos), hcqUpper⟩
  have hlpfCQ : canonicalLargestPrimeFactor (c * q) = q :=
    canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hq hroughQ
  have hcV : c ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcU0 hprePrime
    intro r hr
    exact hroughQ.trans (hpreLarger r hr)
  have hcqV : c * q ∈ V := by
    dsimp [V]
    apply mem_adaptiveCarrier_of_all_larger_primes pre hcqU0 hprePrime
    intro r hr
    rw [hlpfCQ]
    exact hpreLarger r hr
  have hcParent :
      c ∈ squareRootCanonicalRoughFreshPrimeParentsOn q V := by
    apply mem_squareRootCanonicalRoughFreshPrimeParentsOn.mpr
    exact ⟨hcV, hc, hroughQ, hcqV⟩
  rw [hsplit]
  exact squareRootCanonicalRoughAdaptiveRawCoefficient_eq_zero_of_parent_at_split
    pre post U0 (fun _ => (1 : ℂ)) hcParent

/-- The literal geometric range-exit step vanishes on the evolved descending
chronology.  Every top escape or birth is witnessed by a larger prime that has
already killed the inherited parent coefficient. -/
theorem directSumCoupledGeometricRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    directSumCoupledGeometricRangeExitStepMass R p U a = 0 := by
  dsimp
  unfold directSumCoupledGeometricRangeExitStepMass
  apply Finset.sum_eq_zero
  intro c hcParent
  rcases mem_squareRootCanonicalRoughFreshPrimeParentsOn.mp hcParent with
    ⟨_hcU, hcpos, hrough, _hcpU⟩
  by_cases hTop :
      (squareRootCanonicalRoughFreshTopEscapeBoundary R c p).Nonempty
  · rcases hTop with ⟨q, hqTop⟩
    rcases
        (mem_squareRootCanonicalRoughFreshTopEscapeBoundary_iff
          hR hcpos hp hrough).1 hqTop with
      ⟨hqPrime, _hqRough, _hroot, hcqUpper, hpq, _hwall⟩
    have hzero :=
      evolvedRawCoefficient_eq_zero_of_larger_partner_of_completeDescendingPrefix
        qs hcpos hp hqPrime hrough hpq hcqUpper hcomplete
    rw [hzero]
    simp
  · have hTopEmpty :
        squareRootCanonicalRoughFreshTopEscapeBoundary R c p = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hTop
    by_cases hBirth :
        (squareRootCanonicalRoughFreshBirthBoundary R c p).Nonempty
    · rcases hBirth with ⟨q, hqBirth⟩
      rcases
          (mem_squareRootCanonicalRoughFreshBirthBoundary_iff
            hR hcpos hp hrough).1 hqBirth with
        ⟨hqPrime, hpq, _hcqRoot, _hchildRoot, hchildUpper⟩
      have hc_le_pc : c ≤ p * c := by
        simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right c hp.pos
      have hcq_le_pcq : c * q ≤ (p * c) * q :=
        Nat.mul_le_mul_right q hc_le_pc
      have hcqUpper : c * q ≤ squareRootEndpoint R :=
        hcq_le_pcq.trans hchildUpper
      have hzero :=
        evolvedRawCoefficient_eq_zero_of_larger_partner_of_completeDescendingPrefix
          qs hcpos hp hqPrime hrough hpq hcqUpper hcomplete
      rw [hzero]
      simp
    · have hBirthEmpty :
          squareRootCanonicalRoughFreshBirthBoundary R c p = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hBirth
      rw [hTopEmpty, hBirthEmpty]
      simp

/-- Adding the already-compiled mismatch cancellation shows that the full
range-exit contribution at the evolved step is exactly zero. -/
theorem directSumCoupledRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    directSumCoupledRangeExitStepMass R p U a = 0 := by
  dsimp
  unfold directSumCoupledRangeExitStepMass
  rw [directSumCoupledGeometricRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
    R qs hR hp hcomplete]
  have hmismatch :=
    squareRootCanonicalRoughAdaptiveRawMismatchMass_evolved_eq_zero_of_completeDescendingPrefix
      R qs hR hp hcomplete
  rw [hmismatch]
  simp

/-- Therefore the evolved raw boundary itself is only the internal fresh-prime
threshold term.  The geometric range motion contributes no surviving signed
mass on the actual chronology. -/
theorem adaptiveRawBoundaryMass_evolved_eq_freshPrimeThreshold_of_completeDescendingPrefix
    (R : ℕ) {p : ℕ} (qs : List ℕ)
    (hR : 2 ≤ R) (hp : p.Prime)
    (hcomplete : SquareRootCanonicalRoughCompleteDescendingPrefix R p qs) :
    let U0 := Finset.Icc 1 (squareRootEndpoint R)
    let U := squareRootCanonicalRoughAdaptiveCarrier qs U0
    let a := squareRootCanonicalRoughAdaptiveRawCoefficient qs U0
      (fun _ => (1 : ℂ))
    squareRootCanonicalRoughAdaptiveRawBoundaryMass R p U a =
      directSumCoupledFreshPrimeThresholdStepMass R p U a := by
  dsimp
  rw [squareRootCanonicalRoughAdaptiveRawBoundaryMass_eq_freshPrimeThreshold_add_geometricRangeExit]
  rw [directSumCoupledGeometricRangeExitStepMass_evolved_eq_zero_of_completeDescendingPrefix
    R qs hR hp hcomplete]
  simp

end RHLean.Proof
