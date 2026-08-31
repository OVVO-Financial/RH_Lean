import Mathlib
import RHLean.Analysis.SquareRootCanonicalRoughCovariance

/-!
# Fresh-prime finite differences of canonical rough-prime capacity

The canonical rough-prime response has already collapsed to the nonnegative
prime-partner multiplicity

`PR_R(c) = squareRootCanonicalRoughPrimePartnerCount R c`.

This file opens that multiplicity as a literal finite set of fresh prime
extensions.  At the square endpoint `X_R = R^2 - 1`, a prime `q` contributes
exactly when

`P+(c) < q`, `R <= c*q`, and `c*q <= X_R`.

For a fresh prime `p > P+(c)`, passing from `c` to `p*c` therefore has two and
only two geometric effects:

* a parent partner is lost when `q <= p` or when `p*c*q` crosses above `X_R`;
* a child partner is born when `c*q < R <= p*c*q`.

Consequently `PR_R(c) - PR_R(p*c)` is exactly `losses - births`.  Once the fresh
child has itself reached the root, `R <= p*c`, the birth boundary is empty and
`PR_R(p*c)` is literally a subset of `PR_R(c)`.  The finite difference is then
the cardinality of one explicit boundary.

This is an exact Eulerian ancestry law.  No estimate, norm, PNT input, Mertens
bound, covariance hypothesis, or RH input is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Prime partners in one reciprocal-depth layer of the canonical response. -/
def squareRootCanonicalRoughPrimePartnerLayerSet
    (R c z : ℕ) : Finset ℕ :=
  (primeSieveReciprocalInterval
      (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z).filter Nat.Prime

/-- Literal prime-extension support of the complete canonical partner response. -/
def squareRootCanonicalRoughPrimePartnerSet
    (R c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).biUnion
    (squareRootCanonicalRoughPrimePartnerLayerSet R c)

/-- Different reciprocal depths give disjoint prime-partner layers. -/
theorem squareRootCanonicalRoughPrimePartnerLayerSet_pairwiseDisjoint
    (R c : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 (R - 1)))
      (squareRootCanonicalRoughPrimePartnerLayerSet R c) := by
  intro z hz w hw hzw
  rw [Finset.disjoint_left]
  intro q hqz hqw
  have hz0 : 0 < z := by
    exact (Finset.mem_Icc.mp hz).1
  have hw0 : 0 < w := by
    exact (Finset.mem_Icc.mp hw).1
  have hqzI := (Finset.mem_filter.mp hqz).1
  have hqwI := (Finset.mem_filter.mp hqw).1
  have hqzF :
      q ∈ primeSieveQuotientFiber
        (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z := by
    rw [primeSieveQuotientFiber_eq_reciprocalInterval _ _ z hz0]
    exact hqzI
  have hqwF :
      q ∈ primeSieveQuotientFiber
        (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) w := by
    rw [primeSieveQuotientFiber_eq_reciprocalInterval _ _ w hw0]
    exact hqwI
  have hzEq := (mem_primeSieveQuotientFiber.mp hqzF).2.2
  have hwEq := (mem_primeSieveQuotientFiber.mp hqwF).2.2
  exact hzw (hzEq.symm.trans hwEq)

/-- The collapsed canonical response is exactly the cardinality of its literal
prime-extension support. -/
theorem squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card
    (R c : ℕ) :
    squareRootCanonicalRoughPrimePartnerCount R c =
      ((squareRootCanonicalRoughPrimePartnerSet R c).card : ℂ) := by
  unfold squareRootCanonicalRoughPrimePartnerCount
    squareRootCanonicalRoughPrimeMultiplicity
    squareRootCanonicalRoughPrimePartnerSet
  calc
    (∑ z ∈ Finset.Icc 1 (R - 1),
        primeSieveReciprocalPrimeCount
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z) =
      ∑ z ∈ Finset.Icc 1 (R - 1),
        ((squareRootCanonicalRoughPrimePartnerLayerSet R c z).card : ℂ) := by
      apply Finset.sum_congr rfl
      intro z _hz
      rw [primeSieveReciprocalPrimeCount_eq_card]
      rfl
    _ = ∑ z ∈ Finset.Icc 1 (R - 1),
        ∑ _q ∈ squareRootCanonicalRoughPrimePartnerLayerSet R c z, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp
    _ = ∑ _q ∈ (Finset.Icc 1 (R - 1)).biUnion
        (squareRootCanonicalRoughPrimePartnerLayerSet R c), (1 : ℂ) := by
      rw [Finset.sum_biUnion
        (squareRootCanonicalRoughPrimePartnerLayerSet_pairwiseDisjoint R c)]
    _ = (((Finset.Icc 1 (R - 1)).biUnion
        (squareRootCanonicalRoughPrimePartnerLayerSet R c)).card : ℂ) := by
      simp

/-- Direct arithmetic description of the complete partner support. -/
theorem mem_squareRootCanonicalRoughPrimePartnerSet_iff
    {R c q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) :
    q ∈ squareRootCanonicalRoughPrimePartnerSet R c ↔
      q.Prime ∧
        canonicalLargestPrimeFactor c < q ∧
        R ≤ c * q ∧
        c * q ≤ squareRootEndpoint R := by
  constructor
  · intro hq
    rcases Finset.mem_biUnion.mp hq with ⟨z, hz, hqz⟩
    rcases Finset.mem_Icc.mp hz with ⟨hz1, hzR⟩
    rcases Finset.mem_filter.mp hqz with ⟨hqI, hqPrime⟩
    have hz0 : 0 < z := by omega
    have hqF :
        q ∈ primeSieveQuotientFiber
          (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z := by
      rw [primeSieveQuotientFiber_eq_reciprocalInterval _ _ z hz0]
      exact hqI
    rcases mem_primeSieveQuotientFiber.mp hqF with
      ⟨hrough, hqUpper, hdiv⟩
    have hupper : c * q ≤ squareRootEndpoint R := by
      have h := (Nat.le_div_iff_mul_le hc).1 hqUpper
      simpa [Nat.mul_comm] using h
    have hdivGlobal : squareRootEndpoint R / (c * q) = z := by
      rw [← Nat.div_div_eq_div_mul]
      exact hdiv
    have hcqPos : 0 < c * q := Nat.mul_pos hc hqPrime.pos
    have hroot : R ≤ c * q := by
      by_contra hnot
      have hcqPred : c * q ≤ R - 1 := by omega
      have hRmul : R * (c * q) ≤ squareRootEndpoint R := by
        calc
          R * (c * q) ≤ R * (R - 1) :=
            Nat.mul_le_mul_left R hcqPred
          _ ≤ squareRootEndpoint R := by
            unfold squareRootEndpoint
            nlinarith
      have hRleDiv : R ≤ squareRootEndpoint R / (c * q) :=
        (Nat.le_div_iff_mul_le hcqPos).2 hRmul
      rw [hdivGlobal] at hRleDiv
      omega
    exact ⟨hqPrime, hrough, hroot, hupper⟩
  · rintro ⟨hqPrime, hrough, hroot, hupper⟩
    let z := (squareRootEndpoint R / c) / q
    have hqUpper : q ≤ squareRootEndpoint R / c := by
      apply (Nat.le_div_iff_mul_le hc).2
      simpa [Nat.mul_comm] using hupper
    have hz1 : 1 ≤ z := by
      dsimp [z]
      exact (Nat.one_le_div_iff hqPrime.pos).2 hqUpper
    have hcqPos : 0 < c * q := Nat.mul_pos hc hqPrime.pos
    have hXlt : squareRootEndpoint R < R * (c * q) := by
      unfold squareRootEndpoint
      have hRR : R * R ≤ R * (c * q) := Nat.mul_le_mul_left R hroot
      nlinarith
    have hzR : z < R := by
      have hdivLt : squareRootEndpoint R / (c * q) < R :=
        (Nat.div_lt_iff_lt_mul hcqPos).2 hXlt
      dsimp [z]
      rw [Nat.div_div_eq_div_mul]
      exact hdivLt
    apply Finset.mem_biUnion.mpr
    refine ⟨z, Finset.mem_Icc.mpr ⟨hz1, by omega⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hqPrime⟩
    rw [← primeSieveQuotientFiber_eq_reciprocalInterval
      (canonicalLargestPrimeFactor c) (squareRootEndpoint R / c) z
      (by omega : 0 < z)]
    exact mem_primeSieveQuotientFiber.mpr ⟨hrough, hqUpper, rfl⟩

/-- A prime strictly above the largest prime factor of `c` becomes the canonical
largest prime factor after adjoining it. -/
theorem canonicalLargestPrimeFactor_fresh_mul
    {c p : ℕ} (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    canonicalLargestPrimeFactor (p * c) = p := by
  simpa [Nat.mul_comm] using
    (canonicalLargestPrimeFactor_mul_prime_eq_of_rough hc hp hfresh)

/-- Parent partners lost when adjoining the fresh prime `p`. -/
def squareRootCanonicalRoughFreshLossBoundary
    (R c p : ℕ) : Finset ℕ :=
  squareRootCanonicalRoughPrimePartnerSet R c \
    squareRootCanonicalRoughPrimePartnerSet R (p * c)

/-- Child partners that did not yet belong to the parent. -/
def squareRootCanonicalRoughFreshBirthBoundary
    (R c p : ℕ) : Finset ℕ :=
  squareRootCanonicalRoughPrimePartnerSet R (p * c) \
    squareRootCanonicalRoughPrimePartnerSet R c

/-- Exact parent-only boundary: a parent partner is lost precisely at the fresh
prime threshold `q <= p` or at the upper multiplicative wall `X_R < p*c*q`. -/
theorem mem_squareRootCanonicalRoughFreshLossBoundary_iff
    {R c p q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    q ∈ squareRootCanonicalRoughFreshLossBoundary R c p ↔
      q.Prime ∧
        canonicalLargestPrimeFactor c < q ∧
        R ≤ c * q ∧
        c * q ≤ squareRootEndpoint R ∧
        (q ≤ p ∨ squareRootEndpoint R < (p * c) * q) := by
  have hpc : 0 < p * c := Nat.mul_pos hp.pos hc
  have hlpf : canonicalLargestPrimeFactor (p * c) = p :=
    canonicalLargestPrimeFactor_fresh_mul hc hp hfresh
  constructor
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqParent, hqNotChild⟩
    have hpData :=
      (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc).1 hqParent
    refine ⟨hpData.1, hpData.2.1, hpData.2.2.1, hpData.2.2.2.1, ?_⟩
    by_cases hpq : p < q
    · right
      by_contra hnot
      have hchildUpper : (p * c) * q ≤ squareRootEndpoint R :=
        Nat.le_of_not_gt hnot
      have hchildRoot : R ≤ (p * c) * q := by
        calc
          R ≤ c * q := hpData.2.2.1
          _ ≤ (p * c) * q := by
            nlinarith [hp.two_le]
      apply hqNotChild
      apply (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hpc).2
      simpa [hlpf] using
        (show q.Prime ∧ p < q ∧ R ≤ (p * c) * q ∧
            (p * c) * q ≤ squareRootEndpoint R from
          ⟨hpData.1, hpq, hchildRoot, hchildUpper⟩)
    · left
      omega
  · rintro ⟨hqPrime, hrough, hroot, hupper, hloss⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc).2
      ⟨hqPrime, hrough, hroot, hupper⟩, ?_⟩
    intro hqChild
    have hcData :=
      (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hpc).1 hqChild
    rw [hlpf] at hcData
    rcases hloss with hpq | hwall
    · omega
    · exact (Nat.not_lt_of_ge hcData.2.2.2) hwall

/-- Exact child-only boundary: the only genuinely new partners are primes whose
old product lay below the root and whose fresh-prime child crosses it. -/
theorem mem_squareRootCanonicalRoughFreshBirthBoundary_iff
    {R c p q : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    q ∈ squareRootCanonicalRoughFreshBirthBoundary R c p ↔
      q.Prime ∧ p < q ∧ c * q < R ∧
        R ≤ (p * c) * q ∧
        (p * c) * q ≤ squareRootEndpoint R := by
  have hpc : 0 < p * c := Nat.mul_pos hp.pos hc
  have hlpf : canonicalLargestPrimeFactor (p * c) = p :=
    canonicalLargestPrimeFactor_fresh_mul hc hp hfresh
  constructor
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqChild, hqNotParent⟩
    have hcData :=
      (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hpc).1 hqChild
    rw [hlpf] at hcData
    have hparentRough : canonicalLargestPrimeFactor c < q :=
      hfresh.trans hcData.2.1
    have hparentUpper : c * q ≤ squareRootEndpoint R := by
      calc
        c * q ≤ (p * c) * q := by nlinarith [hp.two_le]
        _ ≤ squareRootEndpoint R := hcData.2.2.2
    have hbelow : c * q < R := by
      by_contra hnot
      apply hqNotParent
      exact (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc).2
        ⟨hcData.1, hparentRough, Nat.le_of_not_gt hnot, hparentUpper⟩
    exact ⟨hcData.1, hcData.2.1, hbelow,
      hcData.2.2.1, hcData.2.2.2⟩
  · rintro ⟨hqPrime, hpq, hbelow, hchildRoot, hchildUpper⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hpc).2
      rw [hlpf]
      exact ⟨hqPrime, hpq, hchildRoot, hchildUpper⟩
    · intro hqParent
      have hpData :=
        (mem_squareRootCanonicalRoughPrimePartnerSet_iff hR hc).1 hqParent
      omega

/-- **General fresh-prime capacity law.**  The parent/child response difference
is exactly the cardinality of the loss boundary minus the cardinality of the
root-crossing birth boundary. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (p * c) =
      ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) -
        ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℂ) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card,
    squareRootCanonicalRoughPrimePartnerCount_eq_partnerSet_card]
  have hA := Finset.card_sdiff_add_card_inter
    (squareRootCanonicalRoughPrimePartnerSet R c)
    (squareRootCanonicalRoughPrimePartnerSet R (p * c))
  have hB := Finset.card_sdiff_add_card_inter
    (squareRootCanonicalRoughPrimePartnerSet R (p * c))
    (squareRootCanonicalRoughPrimePartnerSet R c)
  have hInter :
      (squareRootCanonicalRoughPrimePartnerSet R (p * c) ∩
          squareRootCanonicalRoughPrimePartnerSet R c).card =
        (squareRootCanonicalRoughPrimePartnerSet R c ∩
          squareRootCanonicalRoughPrimePartnerSet R (p * c)).card := by
    rw [Finset.inter_comm]
  have hInt :
      ((squareRootCanonicalRoughPrimePartnerSet R c).card : ℤ) -
          ((squareRootCanonicalRoughPrimePartnerSet R (p * c)).card : ℤ) =
        ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℤ) -
          ((squareRootCanonicalRoughFreshBirthBoundary R c p).card : ℤ) := by
    unfold squareRootCanonicalRoughFreshLossBoundary
      squareRootCanonicalRoughFreshBirthBoundary
    omega
  exact_mod_cast hInt

/-- Once the fresh child has reached the root, no new partner can be born. -/
theorem squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hroot : R ≤ p * c) :
    squareRootCanonicalRoughFreshBirthBoundary R c p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqData :=
    (mem_squareRootCanonicalRoughFreshBirthBoundary_iff hR hc hp hfresh).1 hq
  have hcple : p * c ≤ c * q := by
    nlinarith
  have hRle : R ≤ c * q := hroot.trans hcple
  omega

/-- Root-reached fresh children have nested partner capacity. -/
theorem squareRootCanonicalRoughPrimePartnerSet_freshChild_subset_of_root_reached
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hroot : R ≤ p * c) :
    squareRootCanonicalRoughPrimePartnerSet R (p * c) ⊆
      squareRootCanonicalRoughPrimePartnerSet R c := by
  intro q hq
  by_contra hnot
  have hbirth : q ∈ squareRootCanonicalRoughFreshBirthBoundary R c p :=
    Finset.mem_sdiff.mpr ⟨hq, hnot⟩
  rw [squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
    hR hc hp hfresh hroot] at hbirth
  simp at hbirth

/-- **Root-reached finite difference.**  On the ancestry region after first root
crossing, the massive positive partner capacities are nested and their exact
difference is one explicit geometric boundary cardinality. -/
theorem squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_lossBoundary
    {R c p : ℕ} (hR : 2 ≤ R) (hc : 0 < c) (hp : p.Prime)
    (hfresh : canonicalLargestPrimeFactor c < p)
    (hroot : R ≤ p * c) :
    squareRootCanonicalRoughPrimePartnerCount R c -
        squareRootCanonicalRoughPrimePartnerCount R (p * c) =
      ((squareRootCanonicalRoughFreshLossBoundary R c p).card : ℂ) := by
  rw [squareRootCanonicalRoughPrimePartnerCount_sub_freshChild_eq_loss_sub_birth
      hR hc hp hfresh,
    squareRootCanonicalRoughFreshBirthBoundary_eq_empty_of_root_reached
      hR hc hp hfresh hroot]
  simp

end RHLean.Proof