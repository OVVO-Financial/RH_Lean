import Mathlib
import RHLean.Proof.LowPrimeFreshLayerBridge

/-!
# One-sided low-prime sequential dissipation

The running BornPostTail response is already split into exact fresh
largest-prime-factor layers.  This module makes the first genuinely one-sided
piece of that step explicit.

For a fresh prime `p < R`, the singleton cofactor `c = p` is the empty-parent
child.  Its born response is zero, while its high response is a natural
post-root prime-prefix cardinality.  Since `mu(p) = -1`, this atom contributes
with a forced negative sign.

Every other cofactor in the fresh layer has a proper canonical parent.  Those
terms are retained, with the born and high responses still added together, in
one signed bad mass.  They are not duplicated over prime coordinates: membership
itself records `P+(c) = p`, so the same cofactor cannot occur in the bad support
of two distinct fresh primes.

Thus the actual running increment has the exact one-sided form

`Delta_p^born + Delta_p^high = -D_p + F_p`,

where `D_p` is a nonnegative natural cardinality and `F_p` is the globally
assigned proper-parent mass.  No absolute value, Cauchy--Schwarz estimate, PNT,
Mertens bound, covariance normalization, or RH-equivalent statement appears.
The remaining quantitative problem is to control the single globally assigned
proper-parent mass rather than paying a new local defect at every prime.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Cofactors in the born part of the fresh largest-prime layer. -/
def squareRootLowPrimeBornFreshCofactors
    (R p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (squareRootEndpoint R)).filter fun c =>
    canonicalLargestPrimeFactor c = p

/-- Cofactors in the high part of the fresh largest-prime layer. -/
def squareRootLowPrimeHighFreshCofactors
    (R p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    canonicalLargestPrimeFactor c = p

/-- Proper-parent born cofactors: remove the empty-parent atom `c = p`. -/
def squareRootLowPrimeProperBornCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeBornFreshCofactors R p).erase p

/-- Proper-parent high cofactors: remove the empty-parent atom `c = p`. -/
def squareRootLowPrimeProperHighCofactors
    (R p : ℕ) : Finset ℕ :=
  (squareRootLowPrimeHighFreshCofactors R p).erase p

/-- Born component of the actual fresh running increment. -/
def squareRootLowPrimeBornFreshIncrement
    (R p : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeBornFreshCofactors R p,
    canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)

/-- High component of the actual fresh running increment. -/
def squareRootLowPrimeHighFreshIncrement
    (R K j p : ℕ) : ℂ :=
  ∑ c ∈ squareRootLowPrimeHighFreshCofactors R p,
    canonicalMoebiusWeight c *
      (squareRootBornPostTailHighResponse R K j c : ℂ)

/-- The actual fresh increment, with born and high retained together. -/
def squareRootLowPrimeFreshIncrement
    (R K j p : ℕ) : ℂ :=
  squareRootLowPrimeBornFreshIncrement R p +
    squareRootLowPrimeHighFreshIncrement R K j p

/-- Running imbalance used in the sequential energy diagnostic. -/
def squareRootLowPrimeRunningImbalance
    (R K j p : ℕ) : ℂ :=
  1 - squareRootBornPostTailRunningLowPrimeResponse R K j p

/-- Forced deletion carried by the empty-parent fresh child `c = p`. -/
def squareRootLowPrimePrimeDeletionCount
    (R K j p : ℕ) : ℕ :=
  squareRootBornPostTailHighResponse R K j p

/-- All proper-parent terms at one fresh prime, with the born and high channels
kept signed together. -/
def squareRootLowPrimeProperParentBadMass
    (R K j p : ℕ) : ℂ :=
  (∑ c ∈ squareRootLowPrimeProperBornCofactors R p,
      canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ)) +
    ∑ c ∈ squareRootLowPrimeProperHighCofactors R p,
      canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)

/-- Global proper-parent bad mass on a prime interval.  Each cofactor is assigned
by its own canonical largest prime, not copied into an independent error term
for every prime. -/
def squareRootLowPrimeGlobalProperParentBadMass
    (R K j L U : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
    squareRootLowPrimeProperParentBadMass R K j p

private theorem canonicalLargestPrimeFactor_eq_prime
    {p : ℕ} (hp : p.Prime) :
    canonicalLargestPrimeFactor p = p := by
  have hlpfPrime : (canonicalLargestPrimeFactor p).Prime :=
    canonicalLargestPrimeFactor_prime hp.one_lt
  have hlpfDvd : canonicalLargestPrimeFactor p ∣ p :=
    canonicalLargestPrimeFactor_dvd hp.one_lt
  exact (Nat.prime_dvd_prime_iff_eq hlpfPrime hp).mp hlpfDvd

private theorem canonicalMoebiusWeight_prime_eq_neg_one
    {p : ℕ} (hp : p.Prime) :
    canonicalMoebiusWeight p = -1 := by
  unfold canonicalMoebiusWeight
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- A prime cofactor has no born partner: the defining interval would require
simultaneously `p < q` and `q ≤ p`. -/
theorem squareRootBornPartnerCount_prime_eq_zero
    (R : ℕ) {p : ℕ} (hp : p.Prime) :
    squareRootBornPartnerCount R p = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [squareRootBornPartnerSet, Finset.mem_filter] at hq
  rcases hq with ⟨_hqRange, _hqPrime, hrough, hqp, _hproduct⟩
  rw [canonicalLargestPrimeFactor_eq_prime hp] at hrough
  omega

private theorem prime_mem_squareRootLowPrimeBornFreshCofactors
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    p ∈ squareRootLowPrimeBornFreshCofactors R p := by
  have hRX : R ≤ squareRootEndpoint R := by
    have hsq : R + 1 ≤ R ^ 2 := by nlinarith
    unfold squareRootEndpoint
    omega
  unfold squareRootLowPrimeBornFreshCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr
        ⟨hp.one_le, (Nat.le_of_lt hpR).trans hRX⟩,
      canonicalLargestPrimeFactor_eq_prime hp⟩

private theorem prime_mem_squareRootLowPrimeHighFreshCofactors
    {R p : ℕ} (hp : p.Prime) (hpR : p < R) :
    p ∈ squareRootLowPrimeHighFreshCofactors R p := by
  unfold squareRootLowPrimeHighFreshCofactors
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp.one_le, by omega⟩,
      canonicalLargestPrimeFactor_eq_prime hp⟩

/-- The split fresh increment is exactly the existing kernel-checked fresh
cofactor layer. -/
theorem squareRootBornPostTailFreshCofactorLayer_eq_lowPrimeFreshIncrement
    (R K j p : ℕ) :
    squareRootBornPostTailFreshCofactorLayer R K j p =
      squareRootLowPrimeFreshIncrement R K j p := by
  unfold squareRootBornPostTailFreshCofactorLayer
    squareRootLowPrimeFreshIncrement
    squareRootLowPrimeBornFreshIncrement
    squareRootLowPrimeHighFreshIncrement
    squareRootLowPrimeBornFreshCofactors
    squareRootLowPrimeHighFreshCofactors
  rw [Finset.sum_filter, Finset.sum_filter]

/-- The running-state step is the split born-plus-high fresh increment. -/
theorem squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
    (R K j p : ℕ) (hp : p.Prime) :
    squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      squareRootLowPrimeFreshIncrement R K j p := by
  rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_freshCofactorLayer
      R K j p hp,
    squareRootBornPostTailFreshCofactorLayer_eq_lowPrimeFreshIncrement]

/-- Removing the empty-parent prime atom leaves the entire born increment,
because that atom's born response is zero. -/
theorem squareRootLowPrimeBornFreshIncrement_eq_properParent
    {R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeBornFreshIncrement R p =
      ∑ c ∈ squareRootLowPrimeProperBornCofactors R p,
        canonicalMoebiusWeight c * (squareRootBornPartnerCount R c : ℂ) := by
  have hpMem :=
    prime_mem_squareRootLowPrimeBornFreshCofactors hR hp hpR
  unfold squareRootLowPrimeBornFreshIncrement
    squareRootLowPrimeProperBornCofactors
  rw [← Finset.add_sum_erase _
      (fun c => canonicalMoebiusWeight c *
        (squareRootBornPartnerCount R c : ℂ)) hpMem,
    squareRootBornPartnerCount_prime_eq_zero R hp]
  simp

/-- The empty-parent atom contributes exactly the negative natural deletion
count to the high increment. -/
theorem squareRootLowPrimeHighFreshIncrement_eq_neg_deletion_add_properParent
    {R K j p : ℕ} (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeHighFreshIncrement R K j p =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        ∑ c ∈ squareRootLowPrimeProperHighCofactors R p,
          canonicalMoebiusWeight c *
            (squareRootBornPostTailHighResponse R K j c : ℂ) := by
  have hpMem := prime_mem_squareRootLowPrimeHighFreshCofactors hp hpR
  unfold squareRootLowPrimeHighFreshIncrement
    squareRootLowPrimeProperHighCofactors
    squareRootLowPrimePrimeDeletionCount
  rw [← Finset.add_sum_erase _
      (fun c => canonicalMoebiusWeight c *
        (squareRootBornPostTailHighResponse R K j c : ℂ)) hpMem,
    canonicalMoebiusWeight_prime_eq_neg_one hp]
  ring

/-- **One-sided fresh-prime decomposition.**  The actual born-plus-high
increment is a forced negative natural deletion plus one proper-parent bad mass.
No channel is bounded separately. -/
theorem squareRootLowPrimeFreshIncrement_eq_neg_deletion_add_badMass
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    squareRootLowPrimeFreshIncrement R K j p =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        squareRootLowPrimeProperParentBadMass R K j p := by
  unfold squareRootLowPrimeFreshIncrement
    squareRootLowPrimeProperParentBadMass
  rw [squareRootLowPrimeBornFreshIncrement_eq_properParent hR hp hpR,
    squareRootLowPrimeHighFreshIncrement_eq_neg_deletion_add_properParent
      hp hpR]
  ring

/-- The deletion is a genuine nonnegative quantity, not an absolute value
inserted after the fact. -/
theorem squareRootLowPrimePrimeDeletionCount_nonneg
    (R K j p : ℕ) :
    (0 : ℤ) ≤ (squareRootLowPrimePrimeDeletionCount R K j p : ℤ) := by
  positivity

/-- Beyond the shallow cutoff, the forced deletion is exactly the post-root
prime-prefix cardinality at the fresh prime. -/
theorem squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix
    {R K j p : ℕ} (hKp : K < p) :
    squareRootLowPrimePrimeDeletionCount R K j p =
      squareRootPostRootPrimePrefixCard R p := by
  unfold squareRootLowPrimePrimeDeletionCount
    squareRootBornPostTailHighResponse
  rw [if_neg (by omega : ¬ p ≤ K)]

/-- Later prime deletions have no larger geometric post-root prefix than earlier
ones. -/
theorem squareRootLowPrimePrimeDeletionCount_antitone
    {R K j p q : ℕ} (hp : 0 < p) (hpq : p ≤ q)
    (hKp : K < p) (hKq : K < q) :
    squareRootLowPrimePrimeDeletionCount R K j q ≤
      squareRootLowPrimePrimeDeletionCount R K j p := by
  rw [squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix hKq,
    squareRootLowPrimePrimeDeletionCount_eq_postRootPrefix hKp]
  unfold squareRootPostRootPrimePrefixCard
  apply Finset.card_le_card
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨hrIoc, hrPrime⟩
  rcases Finset.mem_Ioc.mp hrIoc with ⟨hRr, hrq⟩
  have hdiv : squareRootEndpoint R / q ≤ squareRootEndpoint R / p :=
    Nat.div_le_div_left hpq hp
  have hmax :
      max R (squareRootEndpoint R / q) ≤
        max R (squareRootEndpoint R / p) :=
    max_le_max_left R hdiv
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hRr, hrq.trans hmax⟩, hrPrime⟩

private theorem lpf_eq_of_mem_properBorn
    {R p c : ℕ} (hc : c ∈ squareRootLowPrimeProperBornCofactors R p) :
    canonicalLargestPrimeFactor c = p := by
  exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2

private theorem lpf_eq_of_mem_properHigh
    {R p c : ℕ} (hc : c ∈ squareRootLowPrimeProperHighCofactors R p) :
    canonicalLargestPrimeFactor c = p := by
  exact (Finset.mem_filter.mp (Finset.mem_erase.mp hc).2).2

/-- Proper-parent born supports for distinct fresh primes are disjoint. -/
theorem squareRootLowPrimeProperBornCofactors_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeProperBornCofactors R p)
      (squareRootLowPrimeProperBornCofactors R q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  exact hpq ((lpf_eq_of_mem_properBorn hcp).symm.trans
    (lpf_eq_of_mem_properBorn hcq))

/-- Proper-parent high supports for distinct fresh primes are disjoint. -/
theorem squareRootLowPrimeProperHighCofactors_disjoint
    {R p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareRootLowPrimeProperHighCofactors R p)
      (squareRootLowPrimeProperHighCofactors R q) := by
  rw [Finset.disjoint_left]
  intro c hcp hcq
  exact hpq ((lpf_eq_of_mem_properHigh hcp).symm.trans
    (lpf_eq_of_mem_properHigh hcq))

/-- A proper-parent cofactor can be assigned to only one fresh prime even when
it contributes to both response channels. -/
theorem squareRootLowPrimeProperParent_support_unique
    {R p q c : ℕ}
    (hcp : c ∈ squareRootLowPrimeProperBornCofactors R p ∨
      c ∈ squareRootLowPrimeProperHighCofactors R p)
    (hcq : c ∈ squareRootLowPrimeProperBornCofactors R q ∨
      c ∈ squareRootLowPrimeProperHighCofactors R q) :
    p = q := by
  have hp : canonicalLargestPrimeFactor c = p := by
    rcases hcp with hcp | hcp
    · exact lpf_eq_of_mem_properBorn hcp
    · exact lpf_eq_of_mem_properHigh hcp
  have hq : canonicalLargestPrimeFactor c = q := by
    rcases hcq with hcq | hcq
    · exact lpf_eq_of_mem_properBorn hcq
    · exact lpf_eq_of_mem_properHigh hcq
  exact hp.symm.trans hq

/-- **SquareRootLowPrimeSequentialDissipation.**  The running prime step has the
accepted one-sided form, and its deletion term is certified nonnegative.  The
only surviving obstruction is the single proper-parent mass on globally
disjoint largest-prime supports. -/
theorem squareRootLowPrimeSequentialDissipation
    {R K j p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) (hpR : p < R) :
    (squareRootBornPostTailRunningLowPrimeResponse R K j p -
        squareRootBornPostTailRunningLowPrimeResponse R K j (p - 1) =
      -((squareRootLowPrimePrimeDeletionCount R K j p : ℕ) : ℂ) +
        squareRootLowPrimeProperParentBadMass R K j p) ∧
      (0 : ℤ) ≤ (squareRootLowPrimePrimeDeletionCount R K j p : ℤ) := by
  constructor
  · rw [squareRootBornPostTailRunningLowPrimeResponse_step_eq_lowPrimeFreshIncrement
      R K j p hp]
    exact squareRootLowPrimeFreshIncrement_eq_neg_deletion_add_badMass
      hR hp hpR
  · exact squareRootLowPrimePrimeDeletionCount_nonneg R K j p

end RHLean.Proof
