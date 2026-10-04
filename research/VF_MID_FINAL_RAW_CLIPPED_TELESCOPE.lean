import Mathlib
import «research.VF_MID_SUBDOUBLING_SURVIVOR_TO_OWNER_GATE»
import «research.VF_MID_PHI_OWNER_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_PAIR_POLARIZATION»
import RHLean.Analysis.SquareRootPrimeCountGap

/-!
# VF final raw clipped telescope entry

This file pushes the merged #886 restricted survivor packet one exact step
farther into the returned-core first-owner geometry.

For a genuine subdoubling frozen run `A <= R < B <= 2A`, every nonzero
restricted survivor site is already known to be clipped at every live first
owner `p > A`.  Therefore the admitted base part of every arbitrary-site
first-owner cell vanishes identically.

The result below is an exact signed identity: each live first-owner cell of the
#885/#886 restricted site is pure

  clipped-base amplitude * restricted-child amplitude.

No norm, reciprocal reweighting, or cancellation estimate is used.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-! ## Subdoubling rank-two normal form: the 317 pattern at every scale -/

/-- **Global rank-two survivor classification.**

On an entire frozen subdoubling run, every surviving site is exactly one of the
two types seen in the hand computations:

* an actual prime, carrying Mobius sign `-1`;
* a product `q*r` of two primes strictly above the frozen cutoff `A`,
  carrying Mobius sign `+1`.

There are no degree-three-or-higher survivor faces. -/
theorem vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
    {A B n : ℕ}
    (hA : 3 ≤ A) (_hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    n.Prime ∨
      ∃ q r : ℕ,
        q.Prime ∧ r.Prime ∧ A < q ∧ q ≤ r ∧ n = q * r := by
  rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
  rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
  have hR2 : 2 ≤ R := by omega
  have hRlt : R < 2 * A := hRB.trans_le hBA
  have hsplit :=
    vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
      (A := A) (R := R) hR2 hAR
  have hmem :
      n ∈ vfMidSquareWheelPrimes R ∪
        vfMidSquareBandPrefixCompositeSurvivors A R := by
    rw [← hsplit]
    exact hnSurv
  rcases Finset.mem_union.mp hmem with hnPrime | hnComp
  · exact Or.inl (Finset.mem_filter.mp hnPrime).2
  · exact Or.inr
      (vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_subdoubling
        hA hAR hRlt hnComp)

/-- The rank-two classification carries the exact signs used in the 210/317
hand ledgers: prime survivors are `-1`, nonprime survivors are `+1`. -/
theorem vfMidDyadicPrefixSurvivor_realMoebiusStep_eq
    {A B n : ℕ}
    (hA : 3 ≤ A) (_hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    realMoebiusStep n = if n.Prime then -1 else 1 := by
  by_cases hnPrime : n.Prime
  · rw [if_pos hnPrime, realMoebiusStep,
      ArithmeticFunction.moebius_apply_prime hnPrime]
    norm_num
  · rw [if_neg hnPrime]
    rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
    rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
    have hR2 : 2 ≤ R := by omega
    have hRlt : R < 2 * A := hRB.trans_le hBA
    have hsplit :=
      vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
        (A := A) (R := R) hR2 hAR
    have hmem :
        n ∈ vfMidSquareWheelPrimes R ∪
          vfMidSquareBandPrefixCompositeSurvivors A R := by
      rw [← hsplit]
      exact hnSurv
    have hnComp :
        n ∈ vfMidSquareBandPrefixCompositeSurvivors A R := by
      rcases Finset.mem_union.mp hmem with hp | hc
      · exact False.elim (hnPrime (Finset.mem_filter.mp hp).2)
      · exact hc
    have hmu :=
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling
        hA hAR hRlt hnComp
    rw [realMoebiusStep, hmu]
    norm_num

/-- **A live owner strips every survivor to degree at most one.**

If a prime owner `p` divides a frozen-run survivor `n`, the returned parent
`n/p` is either `1` (when `n` itself is prime) or another prime.  This is
the exact general form of the 317 computation `323 = 17*19 -> 19`; after the
first live owner there is no hidden composite returned parent. -/
theorem vfMidDyadicPrefixSurvivor_div_prime_eq_one_or_prime
    {A B p n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hpn : p ∣ n) :
    n / p = 1 ∨ (n / p).Prime := by
  rcases
      vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
        hA hAB hBA hn with hnPrime | ⟨q, r, hq, hr, _hAq, _hqr, rfl⟩
  · have hpeq : p = n := by
      rcases (Nat.dvd_prime hnPrime).mp hpn with hp1 | hpnEq
      · exact False.elim (hp.ne_one hp1)
      · exact hpnEq
    left
    subst p
    exact Nat.div_self hnPrime.pos
  · have hpqr : p ∣ q ∨ p ∣ r := hp.dvd_mul.mp hpn
    rcases hpqr with hpq | hpr
    · have hpEqQ : p = q := by
        rcases (Nat.dvd_prime hq).mp hpq with hp1 | hpqEq
        · exact False.elim (hp.ne_one hp1)
        · exact hpqEq
      right
      subst p
      simpa [hq.ne_zero] using hr
    · have hpEqR : p = r := by
        rcases (Nat.dvd_prime hr).mp hpr with hp1 | hprEq
        · exact False.elim (hp.ne_one hp1)
        · exact hprEq
      right
      subst p
      simpa [hr.ne_zero] using hq

/-- **Every composite survivor descends in one strip to a prime below the
frozen square scale.**

For `A >= 4`, a nonprime survivor in the subdoubling run is `p*q` with
`A < p <= q`.  Because the whole run lies below `B^2 <= 4 A^2`, the returned
prime `q` satisfies `q < A^2`, hence `sqrt q < A`.

Thus the positive composite part of the 210/317-type ledger has no recursive
composite child at all: one least-owner strip lands on an actual prime at a
strictly smaller square scale. -/
theorem vfMidDyadicPrefixSurvivor_composite_descends_to_prime_below_frozen
    {A B n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hnPrime : ¬ n.Prime) :
    ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ A < p ∧ p ≤ q ∧
        n = p * q ∧ q < A ^ 2 ∧ Nat.sqrt q < A := by
  rcases
      vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
        (by omega : 3 ≤ A) hAB hBA hn with hprime | hcomp
  · exact False.elim (hnPrime hprime)
  · rcases hcomp with ⟨p, q, hp, hq, hAp, hpq, hnEq⟩
    rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
    have hnSite := (Finset.mem_filter.mp hnSurv).1
    unfold vfMidSquareWheelSites at hnSite
    have hnUpper : n < (R + 1) ^ 2 :=
      (Finset.mem_Ioo.mp hnSite).2
    have hRB : R < B := (Finset.mem_Ico.mp hR).2
    have hR1B : R + 1 ≤ B := by omega
    have hR2B2 : (R + 1) ^ 2 ≤ B ^ 2 :=
      Nat.pow_le_pow_left hR1B 2
    have hnB2 : n < B ^ 2 := hnUpper.trans_le hR2B2
    have hB2 : B ^ 2 ≤ (2 * A) ^ 2 :=
      Nat.pow_le_pow_left hBA 2
    have hn4A2 : n < 4 * A ^ 2 := by
      calc
        n < B ^ 2 := hnB2
        _ ≤ (2 * A) ^ 2 := hB2
        _ = 4 * A ^ 2 := by ring
    have hpLower : A + 1 ≤ p := by omega
    have hqA2 : q < A ^ 2 := by
      by_contra hnot
      have hA2q : A ^ 2 ≤ q := Nat.le_of_not_gt hnot
      have hmul :
          (A + 1) * (A ^ 2) ≤ p * q :=
        Nat.mul_le_mul hpLower hA2q
      have hpoly : 4 * A ^ 2 < (A + 1) * (A ^ 2) := by
        nlinarith
      rw [← hnEq] at hmul
      omega
    refine ⟨p, q, hp, hq, hAp, hpq, hnEq, hqA2, ?_⟩
    exact (Nat.sqrt_lt').2 hqA2

/-- Every prime divisor of a nonprime frozen survivor lies below the frozen
square endpoint `A^2`.  Thus no high first owner can hide inside the
semiprime sector. -/
theorem vfMidDyadicPrefixSurvivor_primeDivisor_lt_frozenSquare_of_composite
    {A B p n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hnPrime : ¬ n.Prime)
    (hpn : p ∣ n) :
    p < A ^ 2 := by
  rcases
      vfMidDyadicPrefixSurvivor_composite_descends_to_prime_below_frozen
        hA hAB hBA hn hnPrime with
    ⟨q, r, hq, hr, _hAq, hqr, hnEq, hrA2, _hsqrt⟩
  rw [hnEq] at hpn
  rcases hp.dvd_mul.mp hpn with hpq | hpr
  · have hpEqQ : p = q :=
      ((Nat.dvd_prime hq).mp hpq).resolve_left hp.ne_one
    subst p
    exact hqr.trans_lt hrA2
  · have hpEqR : p = r :=
      ((Nat.dvd_prime hr).mp hpr).resolve_left hp.ne_one
    subst p
    exact hrA2

/-- Consequently a first-owner coordinate at or above `A^2` can divide only
a prime survivor endpoint. -/
theorem vfMidDyadicPrefixSurvivor_highOwner_divisible_endpoint_prime
    {A B p n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime) (hpHigh : A ^ 2 ≤ p)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hpn : p ∣ n) :
    n.Prime := by
  by_contra hnPrime
  have hpLow :=
    vfMidDyadicPrefixSurvivor_primeDivisor_lt_frozenSquare_of_composite
      hA hAB hBA hp hn hnPrime hpn
  omega

/-- **Exact low-owner / high-prime dichotomy for one survivor site.**

A prime divisor of a frozen survivor has exactly the two forms visible in the
317 ledger:

* high prime site: the survivor itself is prime, the divisor equals that site,
  and the site lies above `A^2`;
* low semiprime owner: the survivor is nonprime, the divisor lies below
  `A^2`, and stripping it leaves another prime.

There is no third owner type on a subdoubling frozen run. -/
theorem vfMidDyadicPrefixSurvivor_primeDivisor_dichotomy
    {A B p n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hpn : p ∣ n) :
    (n.Prime ∧ p = n ∧ A ^ 2 < n) ∨
      (¬ n.Prime ∧ p < A ^ 2 ∧ (n / p).Prime) := by
  have hnAbove : A ^ 2 < n := by
    rcases Finset.mem_biUnion.mp hn with ⟨R, hR, hnSurv⟩
    have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
    have hnSite := (Finset.mem_filter.mp hnSurv).1
    unfold vfMidSquareWheelSites at hnSite
    have hR2n : R ^ 2 < n := (Finset.mem_Ioo.mp hnSite).1
    have hA2R2 : A ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left hAR 2
    exact hA2R2.trans_lt hR2n
  by_cases hnPrime : n.Prime
  · left
    have hpEq : p = n :=
      ((Nat.dvd_prime hnPrime).mp hpn).resolve_left hp.ne_one
    exact ⟨hnPrime, hpEq, hnAbove⟩
  · right
    have hpLow :=
      vfMidDyadicPrefixSurvivor_primeDivisor_lt_frozenSquare_of_composite
        hA hAB hBA hp hn hnPrime hpn
    have hquot :=
      vfMidDyadicPrefixSurvivor_div_prime_eq_one_or_prime
        (by omega : 3 ≤ A) hAB hBA hp hn hpn
    rcases hquot with hquotOne | hquotPrime
    · have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      rw [hquotOne, mul_one] at hmul
      have hnEqP : n = p := hmul.symm
      exact False.elim (hnPrime (hnEqP.symm ▸ hp))
    · exact ⟨hnPrime, hpLow, hquotPrime⟩

/-- **High first-owner fibres are pure prime-prime fibres.**

If the least fresh owner of two frozen survivors lies at or above `A^2`, then
neither endpoint can be a rank-two survivor.  Otherwise one of the endpoint's
prime factors, all of which lie below `A^2`, would already be a smaller fresh
coordinate.  Thus the high part of the first-owner ledger is exactly the
prime-prime sector seen at owners 197,199,... in the 317 computation. -/
theorem vfMidDyadicPrefixSurvivor_highFirstOwner_forces_prime_pair
    {A B p m n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime) (hpHigh : A ^ 2 ≤ p)
    (hm : m ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (howner : IsSquarefreePairFreshPrimeOwner p m n) :
    m.Prime ∧ n.Prime := by
  have hmClock :=
    vfMidDyadicPrefixSurvivorCarrier_subset_lowOwnerNonzero
      (by omega : 3 ≤ A) hAB hBA hm
  have hnClock :=
    vfMidDyadicPrefixSurvivorCarrier_subset_lowOwnerNonzero
      (by omega : 3 ≤ A) hAB hBA hn
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmClock).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnClock).2
  have hpXor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
      hp hmPos hnPos).1 howner.1
  have hmPrime : m.Prime := by
    by_contra hmNotPrime
    have hpNotM : ¬ p ∣ m := by
      intro hpm
      have hpLow :=
        vfMidDyadicPrefixSurvivor_primeDivisor_lt_frozenSquare_of_composite
          hA hAB hBA hp hm hmNotPrime hpm
      omega
    have hpn : p ∣ n := by
      rcases hpXor with hleft | hright
      · exact False.elim (hpNotM hleft.1)
      · exact hright.1
    have hnPrime :=
      vfMidDyadicPrefixSurvivor_highOwner_divisible_endpoint_prime
        hA hAB hBA hp hpHigh hn hpn
    have hpEqN : p = n :=
      ((Nat.dvd_prime hnPrime).mp hpn).resolve_left hp.ne_one
    rcases
        vfMidDyadicPrefixSurvivor_composite_descends_to_prime_below_frozen
          hA hAB hBA hm hmNotPrime with
      ⟨q, r, hq, _hr, _hAq, hqr, hmEq, hrA2, _hsqrt⟩
    have hqLtP : q < p := by omega
    have hqm : q ∣ m := by
      rw [hmEq]
      exact dvd_mul_right q r
    have hqn : ¬ q ∣ n := by
      rw [← hpEqN]
      intro hqp
      have hqEqP :=
        ((Nat.dvd_prime hp).mp hqp).resolve_left hq.ne_one
      omega
    have hqFresh : q ∈ squarefreePairFreshPrimeSet m n :=
      (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
        hq hmPos hnPos).2 (Or.inl ⟨hqm, hqn⟩)
    have hpLeQ := howner.2 q hqFresh
    omega
  have hnPrime : n.Prime := by
    by_contra hnNotPrime
    have hpNotN : ¬ p ∣ n := by
      intro hpn
      have hpLow :=
        vfMidDyadicPrefixSurvivor_primeDivisor_lt_frozenSquare_of_composite
          hA hAB hBA hp hn hnNotPrime hpn
      omega
    have hpm : p ∣ m := by
      rcases hpXor with hleft | hright
      · exact hleft.1
      · exact False.elim (hpNotN hright.1)
    have hmPrimeHigh :=
      vfMidDyadicPrefixSurvivor_highOwner_divisible_endpoint_prime
        hA hAB hBA hp hpHigh hm hpm
    have hpEqM : p = m :=
      ((Nat.dvd_prime hmPrimeHigh).mp hpm).resolve_left hp.ne_one
    rcases
        vfMidDyadicPrefixSurvivor_composite_descends_to_prime_below_frozen
          hA hAB hBA hn hnNotPrime with
      ⟨q, r, hq, _hr, _hAq, hqr, hnEq, hrA2, _hsqrt⟩
    have hqLtP : q < p := by omega
    have hqn : q ∣ n := by
      rw [hnEq]
      exact dvd_mul_right q r
    have hqmNot : ¬ q ∣ m := by
      rw [← hpEqM]
      intro hqp
      have hqEqP :=
        ((Nat.dvd_prime hp).mp hqp).resolve_left hq.ne_one
      omega
    have hqFresh : q ∈ squarefreePairFreshPrimeSet m n :=
      (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
        hq hmPos hnPos).2 (Or.inr ⟨hqn, hqmNot⟩)
    have hpLeQ := howner.2 q hqFresh
    omega
  exact ⟨hmPrime, hnPrime⟩

/-- High first-owner pair weights are therefore exactly `+1`. -/
theorem vfMidDyadicPrefixSurvivor_highFirstOwner_pairWeight_eq_one
    {A B p m n : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime) (hpHigh : A ^ 2 ≤ p)
    (hm : m ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (howner : IsSquarefreePairFreshPrimeOwner p m n) :
    realMoebiusStep m * realMoebiusStep n = 1 := by
  rcases
      vfMidDyadicPrefixSurvivor_highFirstOwner_forces_prime_pair
        hA hAB hBA hp hpHigh hm hn howner with ⟨hmPrime, hnPrime⟩
  rw [realMoebiusStep, realMoebiusStep,
    ArithmeticFunction.moebius_apply_prime hmPrime,
    ArithmeticFunction.moebius_apply_prime hnPrime]
  norm_num

/-! ## Uniform finite owner rank of the frozen packet -/

/-- Every frozen survivor has at most two prime coordinates.  This is the
Boolean-face version of the rank-two normal form. -/
theorem vfMidDyadicPrefixSurvivor_primeFace_card_le_two
    {A B n : ℕ}
    (hA : 3 ≤ A) (_hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    (squarefreePrimeFace n).card ≤ 2 := by
  rcases
      vfMidDyadicPrefixSurvivor_prime_or_two_primes_of_subdoubling
        hA hAB hBA hn with hnPrime | ⟨q, r, hq, hr, _hAq, _hqr, hnEq⟩
  · simp [squarefreePrimeFace, hnPrime.primeFactors]
  · rw [hnEq]
    unfold squarefreePrimeFace
    rw [Nat.primeFactors_mul hq.ne_zero hr.ne_zero]
    calc
      (q.primeFactors ∪ r.primeFactors).card ≤
          q.primeFactors.card + r.primeFactors.card :=
        Finset.card_union_le _ _
      _ = 2 := by simp [hq.primeFactors, hr.primeFactors]

/-- **Uniform fresh-owner rank bound.**

Any pair of frozen survivors differs in at most four prime coordinates.
Consequently every owner-stripping chain on the #885/#886 frozen packet has
depth at most four.  This is the all-scale formal version of the finite owner
ledgers seen in the 317 and 1027 calculations. -/
theorem vfMidDyadicPrefixSurvivor_freshPrimeSet_card_le_four
    {A B m n : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hm : m ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hn : n ∈ vfMidDyadicPrefixSurvivorCarrier A B) :
    (squarefreePairFreshPrimeSet m n).card ≤ 4 := by
  have hmCard :=
    vfMidDyadicPrefixSurvivor_primeFace_card_le_two
      hA hAB hBA hm
  have hnCard :=
    vfMidDyadicPrefixSurvivor_primeFace_card_le_two
      hA hAB hBA hn
  unfold squarefreePairFreshPrimeSet
  calc
    ((squarefreePrimeFace m \ squarefreePrimeFace n) ∪
        (squarefreePrimeFace n \ squarefreePrimeFace m)).card ≤
      (squarefreePrimeFace m \ squarefreePrimeFace n).card +
        (squarefreePrimeFace n \ squarefreePrimeFace m).card :=
      Finset.card_union_le _ _
    _ ≤ (squarefreePrimeFace m).card +
        (squarefreePrimeFace n).card := by
      exact Nat.add_le_add
        (Finset.card_le_card Finset.sdiff_subset)
        (Finset.card_le_card Finset.sdiff_subset)
    _ ≤ 2 + 2 := Nat.add_le_add hmCard hnCard
    _ = 4 := by omega

/-! ## Exact run-level prime / semiprime ledger -/

/-- Total population of frozen-wheel composite survivors across one run. -/
def vfMidDyadicPrefixCompositeSupply (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ((vfMidSquareBandPrefixCompositeSurvivors A R).card : ℝ)

/-- Exact multiplicity-preserving population of stripped frozen-composite
children across a run. -/
def vfMidDyadicFrozenCompositeOwnerChildSupply (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
      ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)

/-- The same rank-two correction written as ordinary prime-count increments
on the reciprocal owner intervals. -/
def vfMidDyadicFrozenCompositePrimeIntervalSupply (A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
      ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
        (Nat.primeCounting (R ^ 2 / p) : ℝ))

/-- **Run survivor population = primes + surviving semiprimes.**

This is the all-scale version of the 317 count `23 = 22 + 1`. -/
theorem vfMidDyadicPrefixSupply_eq_prime_add_composite
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    vfMidDyadicPrefixSupply A A B =
      vfMidDyadicPrimeSupply A B +
        vfMidDyadicPrefixCompositeSupply A B := by
  rw [vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards A A B hAB,
    vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply A B hAB]
  unfold vfMidDyadicPrefixCompositeSupply
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hpart :=
    vfMidSquarePrefixWheelSurvivors_card_eq_prime_add_prefixComposite
      A R (by omega : 2 ≤ R) hAR
  exact_mod_cast hpart

/-- **Run survivor signed mass = semiprimes - primes.**

This is the exact all-scale version of the 317 mass `-21 = 1 - 22`. -/
theorem vfMidDyadicPrefixSurvivorMobiusMassReal_eq_composite_sub_prime
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B =
      vfMidDyadicPrefixCompositeSupply A B -
        vfMidDyadicPrimeSupply A B := by
  unfold vfMidDyadicPrefixSurvivorMobiusMassReal
    vfMidDyadicPrefixCompositeSupply
  rw [vfMidDyadicPrimeSupply_eq_sum_blockPrimeSupply A B hAB,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hRlt : R < 2 * A := hRB.trans_le hBA
  rw [vfMidSquareBandPrefixSurvivorMobiusMassReal_eq_cast]
  have hmass :=
    vfMidSquareBandPrefixSurvivorMobiusMass_eq_composite_sub_prime
      hA hAR hRlt
  exact_mod_cast hmass

/-- **The complete 317 ordered-pair ledger, at every subdoubling scale.**

Write `P` for the number of prime survivors and `C` for the number of
rank-two composite survivors.  Then

`M^2 = (P+C) + P(P-1) + C(C-1) - 2 P C`.

The first term is the diagonal population.  The three remaining terms are,
respectively, ordered prime-prime pairs, ordered composite-composite pairs,
and the two orientations of prime-composite pairs.

For `A=14, B=18`, this specializes to
`441 = 23 + 462 + 0 - 44`. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_population_add_pcLedger
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      vfMidDyadicPrefixSupply A A B +
        vfMidDyadicPrimeSupply A B *
          (vfMidDyadicPrimeSupply A B - 1) +
        vfMidDyadicPrefixCompositeSupply A B *
          (vfMidDyadicPrefixCompositeSupply A B - 1) -
        2 * vfMidDyadicPrimeSupply A B *
          vfMidDyadicPrefixCompositeSupply A B := by
  have hpop :=
    vfMidDyadicPrefixSupply_eq_prime_add_composite hA hAB
  have hmass :=
    vfMidDyadicPrefixSurvivorMobiusMassReal_eq_composite_sub_prime
      hA hAB hBA
  rw [hmass, hpop]
  ring

/-- The off-diagonal signed survivor ledger is therefore exactly the three
explicit population sectors from the preceding theorem. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_sub_population_eq_pcOffDiagonal
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 -
        vfMidDyadicPrefixSupply A A B =
      vfMidDyadicPrimeSupply A B *
          (vfMidDyadicPrimeSupply A B - 1) +
        vfMidDyadicPrefixCompositeSupply A B *
          (vfMidDyadicPrefixCompositeSupply A B - 1) -
        2 * vfMidDyadicPrimeSupply A B *
          vfMidDyadicPrefixCompositeSupply A B := by
  have h :=
    vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_population_add_pcLedger
      hA hAB hBA
  linarith

/-! ## Exact quotient-prime intervals for late semiprime owners -/

/-- On a frozen subdoubling block, one late-owner child fibre is exactly the
ordinary prime set in its quotient interval.  The roughness filter disappears:
every child is prime, and every prime in the interval is automatically rough
below the least owner. -/
theorem vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_subdoubling
    {A R p : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandCompositeOwnerChildren R p =
      (Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter Nat.Prime := by
  have hR3 : 3 ≤ R := hA.trans hAR
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpData := mem_vfMidSquareBandOwnerPrimes.mp hpOwner
  have hpPrime : p.Prime := hpData.1
  have hpLeR : p ≤ R := hpData.2
  have hpSqLe : p * p ≤ R * R :=
    Nat.mul_le_mul hpLeR hpLeR
  have hpLeLower : p ≤ R ^ 2 / p := by
    apply (Nat.le_div_iff_mul_le hpPrime.pos).2
    simpa [pow_two] using hpSqLe
  ext q
  constructor
  · intro hq
    have hqPrime : q.Prime := by
      have hrough : q ∈ vfMidSquareBandOwnerRoughChildren R p := by
        rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
        exact hq
      exact
        vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
          hA hRlt hp hrough
    have hprefix : q ∈ vfMidSquareBandOwnerPrefixChildren R p := by
      rw [← vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren hR3 hpOwner]
      exact hq
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hprefix).1, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hlower, _hupper⟩
    have hpLtQ : p < q := hpLeLower.trans_lt hlower
    have hsurv : lowWheelHighSurvivor (p - 1) q := by
      intro r hr hrDiv
      have hrData := mem_primesUpTo.mp hr
      have hrPrime : r.Prime := hrData.1
      have hrLtP : r < p := by
        have hrLe : r ≤ p - 1 := hrData.2
        have hpPos : 0 < p := hpPrime.pos
        omega
      have hrEqQ : r = q :=
        ((Nat.dvd_prime hqPrime).mp hrDiv).resolve_left hrPrime.ne_one
      omega
    have hprefix : q ∈ vfMidSquareBandOwnerPrefixChildren R p :=
      Finset.mem_filter.mpr ⟨hqIoc, hsurv⟩
    rw [vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren hR3 hpOwner]
    exact hprefix

/-! ## Owner-first collapse of the square-block semiprime list -/

/-- Roots in the frozen run on which p is a live least-prime owner. -/
def vfMidFrozenOwnerRunRoots (A B p : ℕ) : Finset ℕ :=
  (Finset.Ico A B).filter fun R =>
    p ∈ vfMidSquareBandLateOwnerPrimes A R

/-- All stripped children of one fixed least-prime owner across the run. -/
def vfMidFrozenOwnerRunChildren (A B p : ℕ) : Finset ℕ :=
  (vfMidFrozenOwnerRunRoots A B p).biUnion fun R =>
    vfMidSquareBandCompositeOwnerChildren R p

/-- Distinct square blocks give disjoint child fibres for one fixed owner.
Multiplying a common child back by p would otherwise put the same integer in
two disjoint open square blocks. -/
theorem vfMidFrozenOwnerRunChildren_pairwiseDisjoint
    (A B p : ℕ) :
    Set.PairwiseDisjoint (↑(vfMidFrozenOwnerRunRoots A B p))
      (fun R => vfMidSquareBandCompositeOwnerChildren R p) := by
  intro R _hR S _hS hRS
  change Disjoint
    (vfMidSquareBandCompositeOwnerChildren R p)
    (vfMidSquareBandCompositeOwnerChildren S p)
  rw [Finset.disjoint_left]
  intro q hqR hqS
  rcases Finset.mem_image.mp hqR with ⟨nR, hnROwner, hRq⟩
  rcases Finset.mem_image.mp hqS with ⟨nS, hnSOwner, hSq⟩
  have hmulR := vfMidSquareBandCompositeOwner_mul_div hnROwner
  have hmulS := vfMidSquareBandCompositeOwner_mul_div hnSOwner
  have hnREq : nR = p * q := by
    calc
      nR = p * (nR / p) := hmulR.symm
      _ = p * q := by rw [hRq]
  have hnSEq : nS = p * q := by
    calc
      nS = p * (nS / p) := hmulS.symm
      _ = p * q := by rw [hSq]
  have hsame : nR = nS := hnREq.trans hnSEq.symm
  have hcompR := vfMidSquareBandCompositeOwner_mem hnROwner
  have hcompS := vfMidSquareBandCompositeOwner_mem hnSOwner
  have hsiteR := (Finset.mem_filter.mp hcompR.1).1
  have hsiteS := (Finset.mem_filter.mp hcompS.1).1
  unfold vfMidSquareBandSites at hsiteR hsiteS
  rcases Finset.mem_Ioo.mp hsiteR with ⟨hRlo, hRhi⟩
  rcases Finset.mem_Ioo.mp hsiteS with ⟨hSlo, hShi⟩
  rw [hsame] at hRlo hRhi
  rcases lt_or_gt_of_ne hRS with hRltS | hSltR
  · have hsucc : R + 1 ≤ S := by omega
    have hsq : (R + 1) ^ 2 ≤ S ^ 2 :=
      Nat.pow_le_pow_left hsucc 2
    omega
  · have hsucc : S + 1 ≤ R := by omega
    have hsq : (S + 1) ^ 2 ≤ R ^ 2 :=
      Nat.pow_le_pow_left hsucc 2
    omega

/-- **Fixed-owner hyperbola identity.**

Across a whole frozen subdoubling run, the square-block labels disappear:
the stripped children of one least owner p are exactly the actual primes q in
the single interval p < q <= (B^2-1)/p.  This is the all-scale statement
behind the explicit semiprime lists in the hand checks. -/
theorem vfMidFrozenOwnerRunChildren_eq_primeHyperbolaInterval
    {A B p : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime) (hAp : A < p) (hpB : p < B) :
    vfMidFrozenOwnerRunChildren A B p =
      (Finset.Ioc p ((B ^ 2 - 1) / p)).filter Nat.Prime := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_biUnion.mp hq with ⟨R, hRroot, hqChild⟩
    rcases Finset.mem_filter.mp hRroot with ⟨hR, hpLate⟩
    rcases Finset.mem_Ico.mp hR with ⟨hAR, hRB⟩
    have hRlt : R < 2 * A := hRB.trans_le hBA
    have hchildEq :=
      vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_subdoubling
        hA hAR hRlt hpLate
    rw [hchildEq] at hqChild
    rcases Finset.mem_filter.mp hqChild with ⟨hqI, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqI with ⟨hqLower, hqUpper⟩
    have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
      (mem_vfMidSquareBandLateOwnerPrimes.mp hpLate).1
    have hpLeR : p ≤ R :=
      (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).2
    have hpSqLe : p * p ≤ R * R :=
      Nat.mul_le_mul hpLeR hpLeR
    have hpLeFloor : p ≤ R ^ 2 / p := by
      apply (Nat.le_div_iff_mul_le hp.pos).2
      simpa [pow_two] using hpSqLe
    have hpLtQ : p < q := hpLeFloor.trans_lt hqLower
    have hR1B : R + 1 ≤ B := by omega
    have hsq : (R + 1) ^ 2 ≤ B ^ 2 :=
      Nat.pow_le_pow_left hR1B 2
    have hnum : (R + 1) ^ 2 - 1 ≤ B ^ 2 - 1 :=
      Nat.sub_le_sub_right hsq 1
    have hdiv : ((R + 1) ^ 2 - 1) / p ≤ (B ^ 2 - 1) / p :=
      Nat.div_le_div_right hnum
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hpLtQ, hqUpper.trans hdiv⟩, hqPrime⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqI, hqPrime⟩
    rcases Finset.mem_Ioc.mp hqI with ⟨hpq, hqB⟩
    let n : ℕ := p * q
    let R : ℕ := Nat.sqrt n
    have hpSqLtN : p * p < n := by
      dsimp [n]
      exact (Nat.mul_lt_mul_left hp.pos).2 hpq
    have hpR : p ≤ R := by
      dsimp [R]
      apply (Nat.le_sqrt).2
      exact hpSqLtN.le
    have hAR : A ≤ R := hAp.le.trans hpR
    have hnB : n ≤ B ^ 2 - 1 := by
      have hmul := (Nat.le_div_iff_mul_le hp.pos).1 hqB
      dsimp [n]
      simpa [Nat.mul_comm] using hmul
    have hnBsq : n < B ^ 2 := by
      have hBpos : 0 < B := hp.pos.trans_lt hpB
      have hBsqPos : 0 < B ^ 2 := pow_pos hBpos 2
      omega
    have hRB : R < B := by
      dsimp [R]
      exact (Nat.sqrt_lt').2 hnBsq
    have hRmem : R ∈ Finset.Ico A B :=
      Finset.mem_Ico.mpr ⟨hAR, hRB⟩
    have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
      mem_vfMidSquareBandOwnerPrimes.mpr ⟨hp, hpR⟩
    have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes A R :=
      mem_vfMidSquareBandLateOwnerPrimes.mpr ⟨hpOwner, hAp⟩
    have hRsqLe : R ^ 2 ≤ n := by
      dsimp [R]
      exact Nat.sqrt_le' n
    have hRsqLt : R ^ 2 < n := by
      by_contra hnot
      have heq : R ^ 2 = n :=
        Nat.le_antisymm hRsqLe (Nat.le_of_not_gt hnot)
      have hpDvdR2 : p ∣ R ^ 2 := by
        rw [heq]
        dsimp [n]
        exact dvd_mul_right p q
      have hqDvdR2 : q ∣ R ^ 2 := by
        rw [heq]
        dsimp [n]
        exact dvd_mul_left q p
      have hpDvdR : p ∣ R := hp.dvd_of_dvd_pow hpDvdR2
      have hqDvdR : q ∣ R := hqPrime.dvd_of_dvd_pow hqDvdR2
      have hpne : p ≠ q := ne_of_lt hpq
      have hcop : Nat.Coprime p q :=
        (Nat.coprime_primes hp hqPrime).2 hpne
      have hpqDvdR : p * q ∣ R :=
        hcop.mul_dvd_of_dvd_of_dvd hpDvdR hqDvdR
      have hRpos : 0 < R := hp.pos.trans_le hpR
      have hnLeR : n ≤ R := by
        dsimp [n]
        exact Nat.le_of_dvd hRpos hpqDvdR
      have hR2 : 2 ≤ R := hp.two_le.trans hpR
      rw [← heq] at hnLeR
      nlinarith
    have hnNext : n < (R + 1) ^ 2 := by
      dsimp [R]
      exact Nat.lt_succ_sqrt' n
    have hqLower : R ^ 2 / p < q := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      dsimp [n] at hRsqLt
      simpa [Nat.mul_comm] using hRsqLt
    have hqUpper : q ≤ ((R + 1) ^ 2 - 1) / p := by
      apply (Nat.le_div_iff_mul_le hp.pos).2
      have hmul : p * q ≤ (R + 1) ^ 2 - 1 := by
        dsimp [n] at hnNext
        omega
      simpa [Nat.mul_comm] using hmul
    have hRlt : R < 2 * A := hRB.trans_le hBA
    have hchildEq :=
      vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_subdoubling
        hA hAR hRlt hpLate
    have hqChild : q ∈ vfMidSquareBandCompositeOwnerChildren R p := by
      rw [hchildEq]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hqLower, hqUpper⟩, hqPrime⟩
    unfold vfMidFrozenOwnerRunChildren
    exact Finset.mem_biUnion.mpr
      ⟨R, Finset.mem_filter.mpr ⟨hRmem, hpLate⟩, hqChild⟩

/-! ## Run-level least-owner hyperbola collapse -/

/-- Least-prime owners which can occur anywhere in the frozen run. -/
def vfMidFrozenRunOwnerPrimes (A B : ℕ) : Finset ℕ :=
  (Finset.Ioo A B).filter Nat.Prime

@[simp] theorem mem_vfMidFrozenRunOwnerPrimes {A B p : ℕ} :
    p ∈ vfMidFrozenRunOwnerPrimes A B ↔
      p.Prime ∧ A < p ∧ p < B := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpIoo, hpPrime⟩
    rcases Finset.mem_Ioo.mp hpIoo with ⟨hAp, hpB⟩
    exact ⟨hpPrime, hAp, hpB⟩
  · rintro ⟨hpPrime, hAp, hpB⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioo.mpr ⟨hAp, hpB⟩, hpPrime⟩

/-- On one block of the run, the late-owner set is the fixed run-owner set
filtered by the condition p <= R. -/
theorem vfMidSquareBandLateOwnerPrimes_eq_runOwners_filter
    {A B R : ℕ} (hR : R ∈ Finset.Ico A B) :
    vfMidSquareBandLateOwnerPrimes A R =
      (vfMidFrozenRunOwnerPrimes A B).filter fun p => p ≤ R := by
  ext p
  rcases Finset.mem_Ico.mp hR with ⟨_hAR, hRB⟩
  constructor
  · intro hp
    rcases mem_vfMidSquareBandLateOwnerPrimes.mp hp with ⟨hpOwner, hAp⟩
    rcases mem_vfMidSquareBandOwnerPrimes.mp hpOwner with ⟨hpPrime, hpR⟩
    exact Finset.mem_filter.mpr
      ⟨mem_vfMidFrozenRunOwnerPrimes.mpr
        ⟨hpPrime, hAp, hpR.trans_lt hRB⟩, hpR⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpRun, hpR⟩
    rcases mem_vfMidFrozenRunOwnerPrimes.mp hpRun with
      ⟨hpPrime, hAp, _hpB⟩
    exact mem_vfMidSquareBandLateOwnerPrimes.mpr
      ⟨mem_vfMidSquareBandOwnerPrimes.mpr ⟨hpPrime, hpR⟩, hAp⟩

/-- For a fixed run owner, its active square roots are simply the run roots
at or above that owner. -/
theorem vfMidFrozenOwnerRunRoots_eq_filter_ge
    {A B p : ℕ} (hpRun : p ∈ vfMidFrozenRunOwnerPrimes A B) :
    vfMidFrozenOwnerRunRoots A B p =
      (Finset.Ico A B).filter fun R => p ≤ R := by
  ext R
  constructor
  · intro hR
    rcases Finset.mem_filter.mp hR with ⟨hRIco, hpLate⟩
    have hpOwner := (mem_vfMidSquareBandLateOwnerPrimes.mp hpLate).1
    have hpR := (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).2
    exact Finset.mem_filter.mpr ⟨hRIco, hpR⟩
  · intro hR
    rcases Finset.mem_filter.mp hR with ⟨hRIco, hpR⟩
    rcases mem_vfMidFrozenRunOwnerPrimes.mp hpRun with
      ⟨hpPrime, hAp, _hpB⟩
    have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes A R :=
      mem_vfMidSquareBandLateOwnerPrimes.mpr
        ⟨mem_vfMidSquareBandOwnerPrimes.mpr ⟨hpPrime, hpR⟩, hAp⟩
    exact Finset.mem_filter.mpr ⟨hRIco, hpLate⟩

/-- Because the fixed-owner child fibres are disjoint across square blocks,
the cardinality of their union is the sum of their cardinalities. -/
theorem vfMidFrozenOwnerRunChildren_card_eq_sum
    (A B p : ℕ) :
    (vfMidFrozenOwnerRunChildren A B p).card =
      ∑ R ∈ vfMidFrozenOwnerRunRoots A B p,
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
  unfold vfMidFrozenOwnerRunChildren
  calc
    ((vfMidFrozenOwnerRunRoots A B p).biUnion
        (fun R => vfMidSquareBandCompositeOwnerChildren R p)).card =
      ∑ q ∈ (vfMidFrozenOwnerRunRoots A B p).biUnion
        (fun R => vfMidSquareBandCompositeOwnerChildren R p), 1 := by simp
    _ = ∑ R ∈ vfMidFrozenOwnerRunRoots A B p,
        ∑ _q ∈ vfMidSquareBandCompositeOwnerChildren R p, 1 := by
      rw [Finset.sum_biUnion
        (vfMidFrozenOwnerRunChildren_pairwiseDisjoint A B p)]
    _ = ∑ R ∈ vfMidFrozenOwnerRunRoots A B p,
        (vfMidSquareBandCompositeOwnerChildren R p).card := by simp

/-- Reindex the full triangular block/owner census owner-first. -/
theorem vfMidDyadicFrozenCompositeOwnerChildSupply_eq_sum_runOwnerChildren
    (A B : ℕ) :
    vfMidDyadicFrozenCompositeOwnerChildSupply A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ((vfMidFrozenOwnerRunChildren A B p).card : ℝ) := by
  unfold vfMidDyadicFrozenCompositeOwnerChildSupply
  calc
    (∑ R ∈ Finset.Ico A B,
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
        ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)) =
      ∑ R ∈ Finset.Ico A B,
        ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
          if p ≤ R then
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro R hR
            rw [vfMidSquareBandLateOwnerPrimes_eq_runOwners_filter hR,
              Finset.sum_filter]
    _ = ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ∑ R ∈ Finset.Ico A B,
          if p ≤ R then
            ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ)
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ∑ R ∈ vfMidFrozenOwnerRunRoots A B p,
          ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hpRun
            rw [vfMidFrozenOwnerRunRoots_eq_filter_ge hpRun,
              Finset.sum_filter]
    _ = ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ((vfMidFrozenOwnerRunChildren A B p).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro p _hpRun
            have hcard := vfMidFrozenOwnerRunChildren_card_eq_sum A B p
            exact_mod_cast hcard.symm

/-- The entire frozen composite correction is exactly the sum, over least
owners A < p < B, of the prime population p < q <= (B^2-1)/p. -/
theorem vfMidDyadicFrozenCompositeOwnerChildSupply_eq_semiprimeHyperbolaCards
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenCompositeOwnerChildSupply A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        (((Finset.Ioc p ((B ^ 2 - 1) / p)).filter Nat.Prime).card : ℝ) := by
  rw [vfMidDyadicFrozenCompositeOwnerChildSupply_eq_sum_runOwnerChildren]
  apply Finset.sum_congr rfl
  intro p hpRun
  rcases mem_vfMidFrozenRunOwnerPrimes.mp hpRun with
    ⟨hpPrime, hAp, hpB⟩
  rw [vfMidFrozenOwnerRunChildren_eq_primeHyperbolaInterval
    hA hAB hBA hpPrime hAp hpB]

/-- Prime-count form of one fixed-owner hyperbola interval. -/
theorem vfMidFrozenOwnerHyperbolaCard_add_primeCounting
    {A B p : ℕ} (hpRun : p ∈ vfMidFrozenRunOwnerPrimes A B) :
    ((Finset.Ioc p ((B ^ 2 - 1) / p)).filter Nat.Prime).card +
        Nat.primeCounting p =
      Nat.primeCounting ((B ^ 2 - 1) / p) := by
  rcases mem_vfMidFrozenRunOwnerPrimes.mp hpRun with
    ⟨hpPrime, _hAp, hpB⟩
  have hpSqLt : p ^ 2 < B ^ 2 :=
    Nat.pow_lt_pow_left hpB (by omega)
  have hpSqLeSub : p * p ≤ B ^ 2 - 1 := by
    have hBpos : 0 < B := hpPrime.pos.trans_lt hpB
    have hBsqPos : 0 < B ^ 2 := pow_pos hBpos 2
    have hpSqLt' : p * p < B ^ 2 := by
      simpa [pow_two] using hpSqLt
    omega
  have hpLe : p ≤ (B ^ 2 - 1) / p := by
    apply (Nat.le_div_iff_mul_le hpPrime.pos).2
    exact hpSqLeSub
  exact primeCard_Ioc_add_primeCounting_eq hpLe

/-- Same hyperbola with interval cardinalities replaced by ordinary
prime-count differences. -/
theorem vfMidDyadicFrozenCompositeOwnerChildSupply_eq_semiprimeHyperbolaPrimeCounting
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenCompositeOwnerChildSupply A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ((Nat.primeCounting ((B ^ 2 - 1) / p) : ℝ) -
          (Nat.primeCounting p : ℝ)) := by
  rw [vfMidDyadicFrozenCompositeOwnerChildSupply_eq_semiprimeHyperbolaCards
    hA hAB hBA]
  apply Finset.sum_congr rfl
  intro p hpRun
  have hcount := vfMidFrozenOwnerHyperbolaCard_add_primeCounting hpRun
  have hcountR :
      ((((Finset.Ioc p ((B ^ 2 - 1) / p)).filter Nat.Prime).card : ℝ) +
          (Nat.primeCounting p : ℝ)) =
        (Nat.primeCounting ((B ^ 2 - 1) / p) : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- **Actual VF tracking defect in owner-first semiprime-hyperbola form.**

This is the exact general theorem encoded by the hand examples: freeze through
A, count the frozen survivor population deterministically, and add back exactly
the rank-two semiprimes by their unique least-prime owner. -/
theorem vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_semiprimeHyperbola
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B -
        vfMidDyadicPrefixSupply A A B +
        ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
          ((Nat.primeCounting ((B ^ 2 - 1) / p) : ℝ) -
            (Nat.primeCounting p : ℝ)) := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_ownerPrimeChildren
      hA hAB hBA,
    vfMidDyadicFrozenCompositeOwnerChildSupply_eq_semiprimeHyperbolaPrimeCounting
      hA hAB hBA]

/-- Cardinal form of the quotient-prime identity. -/
theorem vfMidSquareBandCompositeOwnerChildren_card_add_primeCounting_lower_eq_upper
    {A R p : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwnerChildren R p).card +
        Nat.primeCounting (R ^ 2 / p) =
      Nat.primeCounting (((R + 1) ^ 2 - 1) / p) := by
  rw [vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_subdoubling
      hA hAR hRlt hp]
  have hnum : R ^ 2 ≤ (R + 1) ^ 2 - 1 := by
    have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    rw [hexp]
    omega
  have hle :
      R ^ 2 / p ≤ ((R + 1) ^ 2 - 1) / p :=
    Nat.div_le_div_right hnum
  exact primeCard_Ioc_add_primeCounting_eq hle

/-- Every upper quotient endpoint occurring in the frozen correction is below
four times the frozen root.  Hence its square-root scale is strictly below
the frozen root once A is at least four. -/
theorem vfMidFrozenOwnerPrimeIntervalUpper_lt_four_mul
    {A B R p : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    ((R + 1) ^ 2 - 1) / p < 4 * A := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  have hR1B : R + 1 ≤ B := by
    have hRB : R < B := (Finset.mem_Ico.mp hR).2
    omega
  have hnumB :
      (R + 1) ^ 2 - 1 < B ^ 2 := by
    have hsq : (R + 1) ^ 2 ≤ B ^ 2 :=
      Nat.pow_le_pow_left hR1B 2
    have hBpos : 0 < B ^ 2 := by
      have hB4 : 4 ≤ B := hA.trans hAB
      positivity
    omega
  have hB4A : B ^ 2 ≤ 4 * A ^ 2 := by
    calc
      B ^ 2 ≤ (2 * A) ^ 2 := Nat.pow_le_pow_left hBA 2
      _ = 4 * A ^ 2 := by ring
  have hnum4A2 :
      (R + 1) ^ 2 - 1 < 4 * A ^ 2 :=
    hnumB.trans_le hB4A
  apply (Nat.div_lt_iff_lt_mul hpPrime.pos).2
  have hpLower : A + 1 ≤ p := by omega
  have hpoly : 4 * A ^ 2 < (4 * A) * (A + 1) := by
    nlinarith
  have hmul :
      (4 * A) * (A + 1) ≤ (4 * A) * p :=
    Nat.mul_le_mul_left (4 * A) hpLower
  exact hnum4A2.trans (hpoly.trans_le hmul)

/-- Therefore every quotient-prime endpoint used by the frozen semiprime
correction lies at a strictly smaller square-root scale. -/
theorem vfMidFrozenOwnerPrimeIntervalUpper_sqrt_lt_frozen
    {A B R p : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    Nat.sqrt (((R + 1) ^ 2 - 1) / p) < A := by
  have hupper :=
    vfMidFrozenOwnerPrimeIntervalUpper_lt_four_mul
      hA hAB hBA hR hp
  have hfour : 4 * A ≤ A ^ 2 := by
    nlinarith
  exact (Nat.sqrt_lt').2 (hupper.trans_le hfour)

/-! ## Linear owner-tagged child form of the VF tracking packet -/

/-- **Frozen composite population = owner-tagged stripped-child population.**

Stripping the least prime owner is injective inside each owner fibre and the
late-owner fibres partition the frozen composite survivors. -/
theorem vfMidDyadicPrefixCompositeSupply_eq_ownerChildSupply
    {A B : ℕ} (hA : 3 ≤ A) (_hAB : A ≤ B) :
    vfMidDyadicPrefixCompositeSupply A B =
      vfMidDyadicFrozenCompositeOwnerChildSupply A B := by
  unfold vfMidDyadicPrefixCompositeSupply
    vfMidDyadicFrozenCompositeOwnerChildSupply
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hR2 : 2 ≤ R := by omega
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards A R hR2
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors A R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  rw [hownersR]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [vfMidSquareBandCompositeOwnerChildren_card]

/-- Every tagged child in the frozen subdoubling correction is an actual prime
strictly below the starting square `A^2`.

This is the general one-step version of `323 = 17*19 -> 19` in the 317
ledger.  The owner tag is retained, so this theorem makes no injectivity claim
between distinct owner fibres. -/
theorem vfMidDyadicFrozenCompositeOwnerChild_prime_below_frozenSquare
    {A B R p q : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hR : R ∈ Finset.Ico A B)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandCompositeOwnerChildren R p) :
    q.Prime ∧ q < A ^ 2 ∧ Nat.sqrt q < A := by
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hRlt : R < 2 * A := hRB.trans_le hBA
  have hR3 : 3 ≤ R := by omega
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hrough :
      q ∈ vfMidSquareBandOwnerRoughChildren R p := by
    rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
    exact hq
  have hqPrime :
      q.Prime :=
    vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
      (by omega : 3 ≤ A) hRlt hp hrough
  rcases Finset.mem_image.mp hq with ⟨n, hnOwner, hqEq⟩
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpA : A < p :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).2
  have hmul := vfMidSquareBandCompositeOwner_mul_div hnOwner
  have hnComp := vfMidSquareBandCompositeOwner_mem hnOwner
  have hnSite := (Finset.mem_filter.mp hnComp.1).1
  have hnUpper : n < (R + 1) ^ 2 := by
    simpa [vfMidSquareBandSites] using (Finset.mem_Ioo.mp hnSite).2
  have hR1B : R + 1 ≤ B := by omega
  have hR2B2 : (R + 1) ^ 2 ≤ B ^ 2 :=
    Nat.pow_le_pow_left hR1B 2
  have hB2 : B ^ 2 ≤ (2 * A) ^ 2 :=
    Nat.pow_le_pow_left hBA 2
  have hn4A2 : n < 4 * A ^ 2 := by
    calc
      n < (R + 1) ^ 2 := hnUpper
      _ ≤ B ^ 2 := hR2B2
      _ ≤ (2 * A) ^ 2 := hB2
      _ = 4 * A ^ 2 := by ring
  have hpLower : A + 1 ≤ p := by omega
  have hqA2 : q < A ^ 2 := by
    by_contra hnot
    have hA2q : A ^ 2 ≤ q := Nat.le_of_not_gt hnot
    have hprod :
        (A + 1) * A ^ 2 ≤ p * q :=
      Nat.mul_le_mul hpLower hA2q
    have hpoly : 4 * A ^ 2 < (A + 1) * A ^ 2 := by
      nlinarith
    have hnEq : n = p * q := by
      rw [← hqEq] at hmul
      exact hmul.symm
    rw [← hnEq] at hprod
    omega
  exact ⟨hqPrime, hqA2, (Nat.sqrt_lt').2 hqA2⟩

/-- Actual-prime reciprocal interval attached to one square-block owner. -/
def vfMidFrozenOwnerPrimeChildInterval (R p : ℕ) : Finset ℕ :=
  (Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter Nat.Prime

/-- **On a frozen subdoubling run the owner child fibre is literally a prime
interval.**

The generic owner-prefix theorem gives a rough survivor interval.  In the
depth-two subdoubling geometry every such child is prime; conversely a prime in
the same interval is automatically rough above `p-1`. -/
theorem vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_frozen
    {A R p : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandCompositeOwnerChildren R p =
      vfMidFrozenOwnerPrimeChildInterval R p := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpLeR : p ≤ R :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).2
  have hR3 : 3 ≤ R := by omega
  rw [vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren hR3 hpOwner]
  unfold vfMidSquareBandOwnerPrefixChildren
    vfMidFrozenOwnerPrimeChildInterval
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hqI, hsurv⟩
    have hqChild :
        q ∈ vfMidSquareBandCompositeOwnerChildren R p := by
      rw [vfMidSquareBandCompositeOwnerChildren_eq_prefixChildren hR3 hpOwner]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hqI, hsurv⟩
    have hrough :
        q ∈ vfMidSquareBandOwnerRoughChildren R p := by
      rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
      exact hqChild
    have hqPrime :=
      vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
        hA hRlt hp hrough
    exact ⟨hqI, hqPrime⟩
  · rintro ⟨hqI, hqPrime⟩
    refine ⟨hqI, ?_⟩
    intro s hs hsd
    have hsPrime : s.Prime := prime_of_mem_primesUpTo hs
    have hsLe : s ≤ p - 1 := (mem_primesUpTo.mp hs).2
    have hsq : s = q :=
      (Nat.prime_dvd_prime_iff_eq hsPrime hqPrime).mp hsd
    have hpSqLe : p * p ≤ R * R :=
      Nat.mul_le_mul hpLeR hpLeR
    have hpLeFloor : p ≤ R ^ 2 / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [pow_two] using hpSqLe
    have hpLtQ : p < q := hpLeFloor.trans_lt hqI.1
    omega

/-- Hence every frozen owner fibre cardinality is an exact reciprocal
prime-window cardinality. -/
theorem vfMidSquareBandCompositeOwner_card_eq_primeIntervalCard_of_frozen
    {A R p : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card =
      (vfMidFrozenOwnerPrimeChildInterval R p).card := by
  rw [← vfMidSquareBandCompositeOwnerChildren_card R p,
    vfMidSquareBandCompositeOwnerChildren_eq_primeInterval_of_frozen
      hA hAR hRlt hp]

/-- **Exact reciprocal-prime-window form of the positive frozen correction.**

The rank-two correction is the nested sum of literal prime-window populations,
one for each late least-prime owner in each square block. -/
theorem vfMidDyadicPrefixCompositeSupply_eq_sum_primeIntervalCards
    {A B : ℕ}
    (hA : 3 ≤ A) (_hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixCompositeSupply A B =
      ∑ R ∈ Finset.Ico A B,
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
          ((vfMidFrozenOwnerPrimeChildInterval R p).card : ℝ) := by
  unfold vfMidDyadicPrefixCompositeSupply
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hRlt : R < 2 * A := hRB.trans_le hBA
  have howners :=
    vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards
      A R (by omega : 2 ≤ R)
  have hownersR :
      ((vfMidSquareBandPrefixCompositeSurvivors A R).card : ℝ) =
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
          ((vfMidSquareBandCompositeOwner R p).card : ℝ) := by
    exact_mod_cast howners
  rw [hownersR]
  apply Finset.sum_congr rfl
  intro p hp
  rw [vfMidSquareBandCompositeOwner_card_eq_primeIntervalCard_of_frozen
    hA hAR hRlt hp]

/-- **Linear frozen-run VF identity.**

The affine Mobius decoder collapses exactly to

`Tracking = VFMass - frozen survivor population + surviving composite population`.

Equivalently, the only arithmetic correction to the deterministic
`VFMass - frozenSupply` baseline is the rank-two composite population. -/
theorem vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_composite
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B -
        vfMidDyadicPrefixSupply A A B +
        vfMidDyadicPrefixCompositeSupply A B := by
  have htrack :=
    vfMidDyadicVFTrackingDefect_eq_frozenWheel_add_half_moebius
      hA hAB hBA
  have hpop :=
    vfMidDyadicPrefixSupply_eq_prime_add_composite hA hAB
  have hmass :=
    vfMidDyadicPrefixSurvivorMobiusMassReal_eq_composite_sub_prime
      hA hAB hBA
  rw [htrack, hpop, hmass]
  ring

/-- **Owner-tagged prime-child normal form of the actual VF tracking defect.**

On a subdoubling frozen run the correction is not an opaque Mobius remainder:
it is exactly the multiplicity-preserving population of prime children obtained
by stripping the late semiprime owners.  Every such child is one prime below
the starting square by
`vfMidDyadicFrozenCompositeOwnerChild_prime_below_frozenSquare`. -/
theorem vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_ownerPrimeChildren
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B -
        vfMidDyadicPrefixSupply A A B +
        vfMidDyadicFrozenCompositeOwnerChildSupply A B := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_composite
      hA hAB hBA,
    vfMidDyadicPrefixCompositeSupply_eq_ownerChildSupply hA hAB]

/-! ## Fixed-owner reciprocal telescope -/

/-- The upper quotient of one square block matches the lower quotient of the
next block.  The only possible obstruction would be `p | (R+1)^2`, but on a
frozen subdoubling row we have `p < R+1 < 2p`, so that cannot occur. -/
theorem vfMidFrozenOwner_adjacentQuotientEndpoint_eq
    {A R p : ℕ}
    (hp : p.Prime) (hAp : A < p) (hpR : p ≤ R) (hRlt : R < 2 * A) :
    (((R + 1) ^ 2 - 1) / p) = ((R + 1) ^ 2 / p) := by
  have hR1lt2p : R + 1 < 2 * p := by
    have hR1le : R + 1 ≤ 2 * A := by omega
    have h2Alt : 2 * A < 2 * p := by omega
    omega
  have hpNotSucc : ¬ p ∣ R + 1 := by
    intro hdiv
    rcases hdiv with ⟨k, hk⟩
    have hk2 : 2 ≤ k := by
      by_contra hnot
      have hkLe : k ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst k
        simp at hk
      · have hk1 : k = 1 := by omega
        subst k
        simp at hk
        omega
    have h2p : 2 * p ≤ R + 1 := by
      calc
        2 * p ≤ k * p := Nat.mul_le_mul_right p hk2
        _ = p * k := by ring
        _ = R + 1 := hk.symm
    omega
  have hpNotSq : ¬ p ∣ (R + 1) ^ 2 := by
    intro hsq
    exact hpNotSucc (hp.dvd_of_dvd_pow hsq)
  let N : ℕ := (R + 1) ^ 2
  have hmodNe : N % p ≠ 0 := by
    intro hz
    apply hpNotSq
    exact Nat.dvd_iff_mod_eq_zero.mpr hz
  have hmodPos : 1 ≤ N % p :=
    Nat.one_le_iff_ne_zero.mpr hmodNe
  have hdecomp : p * (N / p) + N % p = N :=
    Nat.div_add_mod N p
  apply le_antisymm
  · exact Nat.div_le_div_right (Nat.sub_le N 1)
  · apply (Nat.le_div_iff_mul_le hp.pos).2
    change (N / p) * p ≤ N - 1
    rw [Nat.mul_comm]
    omega

/-- Generic real finite-difference telescope on a natural interval. -/
private theorem vfMidFrozen_sum_increment_Ico
    (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Ico a b, (f (k + 1) - f k)) =
      f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f b,
    Finset.sum_range_sub f a]
  abel

/-- Prime-count contribution of one fixed frozen owner across all square
blocks in which it can occur. -/
def vfMidFrozenFixedOwnerPrimeIntervalSupply (p B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico p B,
    ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
      (Nat.primeCounting (R ^ 2 / p) : ℝ))

/-- **Fixed-owner block telescope.**

For one prime owner `A < p < B <= 2A`, all of its adjacent reciprocal
prime-count intervals telescope exactly:

`sum_{p <= R < B} [pi(((R+1)^2-1)/p)-pi(R^2/p)]
    = pi(B^2/p)-pi(p)`.

This is the whole-run version of the single `17 -> 19` row in the 317
example. -/
theorem vfMidFrozenFixedOwnerPrimeIntervalSupply_eq_endpointGap
    {A B p : ℕ}
    (_hA : 3 ≤ A) (hp : p.Prime) (hAp : A < p)
    (hpB : p < B) (hBA : B ≤ 2 * A) :
    vfMidFrozenFixedOwnerPrimeIntervalSupply p B =
      (Nat.primeCounting (B ^ 2 / p) : ℝ) -
        (Nat.primeCounting p : ℝ) := by
  unfold vfMidFrozenFixedOwnerPrimeIntervalSupply
  have hterm :
      ∀ R ∈ Finset.Ico p B,
        ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
          (Nat.primeCounting (R ^ 2 / p) : ℝ)) =
        ((Nat.primeCounting ((R + 1) ^ 2 / p) : ℝ) -
          (Nat.primeCounting (R ^ 2 / p) : ℝ)) := by
    intro R hR
    have hpR : p ≤ R := (Finset.mem_Ico.mp hR).1
    have hRB : R < B := (Finset.mem_Ico.mp hR).2
    have hRlt : R < 2 * A := hRB.trans_le hBA
    rw [vfMidFrozenOwner_adjacentQuotientEndpoint_eq
      hp hAp hpR hRlt]
  calc
    (∑ R ∈ Finset.Ico p B,
      ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
        (Nat.primeCounting (R ^ 2 / p) : ℝ))) =
      ∑ R ∈ Finset.Ico p B,
        ((Nat.primeCounting ((R + 1) ^ 2 / p) : ℝ) -
          (Nat.primeCounting (R ^ 2 / p) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro R hR
            exact hterm R hR
    _ = (Nat.primeCounting (B ^ 2 / p) : ℝ) -
        (Nat.primeCounting (p ^ 2 / p) : ℝ) := by
          exact vfMidFrozen_sum_increment_Ico
            (fun R => (Nat.primeCounting (R ^ 2 / p) : ℝ))
            (by omega : p ≤ B)
    _ = (Nat.primeCounting (B ^ 2 / p) : ℝ) -
        (Nat.primeCounting p : ℝ) := by
          have hp0 : p ≠ 0 := hp.ne_zero
          simp [pow_two, hp0]

/-- **Triangular finite Fubini for the frozen prime intervals.**

The block-first owner sum is exactly the owner-first sum of the fixed-owner
rows.  This is only a reindexing of the finite triangular carrier

`A <= R < B,quad A < p <= R,quad p prime`.

No estimate or multiplicity collapse occurs. -/
theorem vfMidDyadicFrozenCompositePrimeIntervalSupply_eq_sum_fixedOwner
    {A B : ℕ} (hAB : A ≤ B) :
    vfMidDyadicFrozenCompositePrimeIntervalSupply A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        vfMidFrozenFixedOwnerPrimeIntervalSupply p B := by
  unfold vfMidDyadicFrozenCompositePrimeIntervalSupply
    vfMidFrozenRunOwnerPrimes
    vfMidFrozenFixedOwnerPrimeIntervalSupply
  let atom : ℕ → ℕ → ℝ := fun R p =>
    (Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
      (Nat.primeCounting (R ^ 2 / p) : ℝ)
  have hblock :
      ∀ R ∈ Finset.Ico A B,
        (∑ p ∈ vfMidSquareBandLateOwnerPrimes A R, atom R p) =
          ∑ p ∈ (Finset.Ioo A B).filter Nat.Prime,
            if p ≤ R then atom R p else 0 := by
    intro R hR
    have hRB : R < B := (Finset.mem_Ico.mp hR).2
    rw [vfMidSquareBandLateOwnerPrimes_eq_Ioc_filter_prime A R]
    have hset :
        (Finset.Ioc A R).filter Nat.Prime =
          ((Finset.Ioo A B).filter Nat.Prime).filter (fun p => p ≤ R) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioo]
      constructor
      · rintro ⟨⟨hAp, hpR⟩, hpPrime⟩
        exact ⟨⟨⟨hAp, hpR.trans_lt hRB⟩, hpPrime⟩, hpR⟩
      · rintro ⟨⟨⟨hAp, _hpB⟩, hpPrime⟩, hpR⟩
        exact ⟨⟨hAp, hpR⟩, hpPrime⟩
    rw [hset, Finset.sum_filter]
  calc
    (∑ R ∈ Finset.Ico A B,
      ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
        ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
          (Nat.primeCounting (R ^ 2 / p) : ℝ))) =
      ∑ R ∈ Finset.Ico A B,
        ∑ p ∈ (Finset.Ioo A B).filter Nat.Prime,
          if p ≤ R then atom R p else 0 := by
            apply Finset.sum_congr rfl
            intro R hR
            simpa [atom] using hblock R hR
    _ = ∑ p ∈ (Finset.Ioo A B).filter Nat.Prime,
        ∑ R ∈ Finset.Ico A B,
          if p ≤ R then atom R p else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ p ∈ (Finset.Ioo A B).filter Nat.Prime,
        ∑ R ∈ Finset.Ico p B, atom R p := by
          apply Finset.sum_congr rfl
          intro p hpMem
          rcases Finset.mem_filter.mp hpMem with ⟨hpIoo, _hpPrime⟩
          rcases Finset.mem_Ioo.mp hpIoo with ⟨hAp, hpB⟩
          have hsetR :
              (Finset.Ico A B).filter (fun R => p ≤ R) =
                Finset.Ico p B := by
            ext R
            simp only [Finset.mem_filter, Finset.mem_Ico]
            constructor
            · rintro ⟨⟨hAR, hRB⟩, hpR⟩
              exact ⟨hpR, hRB⟩
            · rintro ⟨hpR, hRB⟩
              exact ⟨⟨hAp.le.trans hpR, hRB⟩, hpR⟩
          rw [← Finset.sum_filter, hsetR]
    _ = ∑ p ∈ (Finset.Ioo A B).filter Nat.Prime,
        ∑ R ∈ Finset.Ico p B,
          ((Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) -
            (Nat.primeCounting (R ^ 2 / p) : ℝ)) := by
          rfl

/-- **Whole-run owner collapse.**

After the triangular Fubini, every fixed owner row telescopes.  Hence the
entire rank-two composite correction is

`sum_{A < p < B, p prime} [pi(B^2/p) - pi(p)]`.

For the 317 run `A=14, B=18`, the owner set is `{17}` and this is exactly
`pi(324/17)-pi(17)=pi(19)-pi(17)=1`. -/
theorem vfMidDyadicFrozenCompositePrimeIntervalSupply_eq_sum_endpointGaps
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenCompositePrimeIntervalSupply A B =
      ∑ p ∈ vfMidFrozenRunOwnerPrimes A B,
        ((Nat.primeCounting (B ^ 2 / p) : ℝ) -
          (Nat.primeCounting p : ℝ)) := by
  rw [vfMidDyadicFrozenCompositePrimeIntervalSupply_eq_sum_fixedOwner hAB]
  apply Finset.sum_congr rfl
  intro p hpMem
  rcases Finset.mem_filter.mp hpMem with ⟨hpIoo, hpPrime⟩
  rcases Finset.mem_Ioo.mp hpIoo with ⟨hAp, hpB⟩
  exact vfMidFrozenFixedOwnerPrimeIntervalSupply_eq_endpointGap
    hA hpPrime hAp hpB hBA

/-! ## Run-level lower-prime-count normal form -/

/-- **Owner-child supply = lower prime-count interval supply.**

Every rank-two frozen composite is therefore represented by one ordinary
prime-count increment at a strictly smaller square-root scale. -/
theorem vfMidDyadicFrozenCompositeOwnerChildSupply_eq_primeIntervalSupply
    {A B : ℕ}
    (hA : 4 ≤ A) (_hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicFrozenCompositeOwnerChildSupply A B =
      vfMidDyadicFrozenCompositePrimeIntervalSupply A B := by
  unfold vfMidDyadicFrozenCompositeOwnerChildSupply
    vfMidDyadicFrozenCompositePrimeIntervalSupply
  apply Finset.sum_congr rfl
  intro R hR
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRB : R < B := (Finset.mem_Ico.mp hR).2
  have hRlt : R < 2 * A := hRB.trans_le hBA
  apply Finset.sum_congr rfl
  intro p hp
  have hcount :=
    vfMidSquareBandCompositeOwnerChildren_card_add_primeCounting_lower_eq_upper
      (by omega : 3 ≤ A) hAR hRlt hp
  have hcountR :
      ((vfMidSquareBandCompositeOwnerChildren R p).card : ℝ) +
          (Nat.primeCounting (R ^ 2 / p) : ℝ) =
        (Nat.primeCounting (((R + 1) ^ 2 - 1) / p) : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- **Actual VF tracking defect in lower-prime-count coordinates.**

This is the literal all-scale generalization of the hand ledgers: deterministic
VF mass minus the frozen survivor supply, plus a finite sum of actual prime
count increments whose square-root scales are all below the frozen root. -/
theorem vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_lowerPrimeIntervals
    {A B : ℕ}
    (hA : 4 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B -
        vfMidDyadicPrefixSupply A A B +
        vfMidDyadicFrozenCompositePrimeIntervalSupply A B := by
  rw [vfMidDyadicVFTrackingDefect_eq_vfMass_sub_prefix_add_ownerPrimeChildren
      (by omega : 3 ≤ A) hAB hBA,
    vfMidDyadicFrozenCompositeOwnerChildSupply_eq_primeIntervalSupply
      hA hAB hBA]

/-- Restricted #886 signed mass on the clipped p-free base side of one
first-owner/signature cell. -/
def vfMidSurvivorClippedBaseAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B a

/-- Restricted #886 signed mass on the p-divisible child side of one
first-owner/signature cell. -/
def vfMidSurvivorChildAmplitude
    (A B p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
    vfMidDyadicPrefixSurvivorSignedSite A B b

/-- Returned admitted parents whose p-child is still on the frozen #886
survivor carrier.  This is the exact lower-coordinate image of the restricted
child fibre under b |-> b / p. -/
def vfMidSurvivorReturnedParentFiber
    (A B p : ℕ) (sig : Finset ℕ) : Finset ℕ :=
  (lowOwnerFirstOwnerAdmittedBaseFiber B p sig).filter fun c =>
    p * c ∈ vfMidDyadicPrefixSurvivorCarrier A B

/-- **Exact child-to-returned-parent reindexing on the frozen carrier.**

A restricted p-child returns uniquely to an admitted p-free parent.  Fresh
prime multiplication reverses the Mobius sign, so the whole restricted child
amplitude is the negative signed mass of this literal returned-parent fibre. -/
theorem vfMidSurvivorChildAmplitude_eq_neg_returnedParents
    {A B p : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidSurvivorChildAmplitude A B p sig =
      ∑ c ∈ vfMidSurvivorReturnedParentFiber A B p sig,
        -realMoebiusStep c := by
  unfold vfMidSurvivorChildAmplitude
    vfMidDyadicPrefixSurvivorSignedSite
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun b _hb => b / p)
    ?_ ?_ ?_ ?_
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbChild, hbCar⟩
    have hcAdm :=
      lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hcancel : p * (b / p) = b :=
      Nat.mul_div_cancel' hbDvd
    unfold vfMidSurvivorReturnedParentFiber
    exact Finset.mem_filter.mpr
      ⟨hcAdm, by simpa [hcancel] using hbCar⟩
  · intro b hb d hd heq
    have hbChild := (Finset.mem_filter.mp hb).1
    have hdChild := (Finset.mem_filter.mp hd).1
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hdDvd : p ∣ d :=
      (Finset.mem_filter.mp hdChild).2.2
    change b / p = d / p at heq
    calc
      b = p * (b / p) := (Nat.mul_div_cancel' hbDvd).symm
      _ = p * (d / p) := by rw [heq]
      _ = d := Nat.mul_div_cancel' hdDvd
  · intro c hc
    have hcData := Finset.mem_filter.mp hc
    have hcAdm := hcData.1
    have hpcCar := hcData.2
    have hpcChild :=
      lowOwnerFirstOwner_mul_mem_child_of_admitted hp hcAdm
    refine ⟨p * c, Finset.mem_filter.mpr ⟨hpcChild, hpcCar⟩, ?_⟩
    simpa [Nat.mul_comm] using Nat.mul_div_left c hp.pos
  · intro b hb
    have hbChild := (Finset.mem_filter.mp hb).1
    have hcBase :=
      lowOwnerFirstOwner_div_mem_base_of_child hp hbChild
    have hnot : ¬ p ∣ b / p :=
      (Finset.mem_filter.mp hcBase).2.2
    have hbDvd : p ∣ b :=
      (Finset.mem_filter.mp hbChild).2.2
    have hcancel : p * (b / p) = b :=
      Nat.mul_div_cancel' hbDvd
    calc
      realMoebiusStep b =
          realMoebiusStep (p * (b / p)) := by rw [hcancel]
      _ = -realMoebiusStep (b / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hnot

/-- Every live post-frozen owner has zero restricted survivor mass on the
admitted p-free base fibre. -/
theorem sum_admitted_vfMidSurvivorSignedSite_eq_zero
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  exact
    vfMidDyadicPrefixSurvivorSignedSite_eq_zero_on_admitted_liveOwner
      hA hAB hBA hpA ha

/-- Hence the complete restricted p-free base sum is literally its clipped
part.  This is the raw signed carrier statement needed before any energy
conversion. -/
theorem sum_base_vfMidSurvivorSignedSite_eq_clipped
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
      vfMidDyadicPrefixSurvivorSignedSite A B a) =
      vfMidSurvivorClippedBaseAmplitude A B p sig := by
  have hsplit :
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) =
        (∑ a ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a) +
        ∑ a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a := by
    unfold lowOwnerFirstOwnerAdmittedBaseFiber
      lowOwnerFirstOwnerClippedBaseFiber
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (s := lowOwnerFirstOwnerBaseFiber B p sig)
        (p := fun a => p * a ≤ squareRootEndpoint B)
        (f := vfMidDyadicPrefixSurvivorSignedSite A B)).symm
  rw [hsplit, sum_admitted_vfMidSurvivorSignedSite_eq_zero
    hA hAB hBA hpA]
  simp [vfMidSurvivorClippedBaseAmplitude]

/-- **Pure clipped-cell form of every live #886 first-owner cell.**

Because the restricted site vanishes on admitted parents, its arbitrary-site
base x child Gram has no admitted-base contribution left. -/
theorem lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    {A B p : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hpA : A < p) :
    lowOwnerFirstOwnerCellGramWith B p sig
        (vfMidDyadicPrefixSurvivorSignedSite A B) =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
  unfold lowOwnerFirstOwnerCellGramWith
  calc
    (∑ ab ∈ (lowOwnerFirstOwnerBaseFiber B p sig).product
        (lowOwnerFirstOwnerChildFiber B p sig),
      vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
        vfMidDyadicPrefixSurvivorSignedSite A B ab.2) =
      ∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        ∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
          vfMidDyadicPrefixSurvivorSignedSite A B a *
            vfMidDyadicPrefixSurvivorSignedSite A B b := by
          simpa only using
            (Finset.sum_product
              (s := lowOwnerFirstOwnerBaseFiber B p sig)
              (t := lowOwnerFirstOwnerChildFiber B p sig)
              (f := fun ab : ℕ × ℕ =>
                vfMidDyadicPrefixSurvivorSignedSite A B ab.1 *
                  vfMidDyadicPrefixSurvivorSignedSite A B ab.2))
    _ =
      (∑ a ∈ lowOwnerFirstOwnerBaseFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B a) *
      (∑ b ∈ lowOwnerFirstOwnerChildFiber B p sig,
        vfMidDyadicPrefixSurvivorSignedSite A B b) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      vfMidSurvivorClippedBaseAmplitude A B p sig *
        vfMidSurvivorChildAmplitude A B p sig := by
          rw [sum_base_vfMidSurvivorSignedSite_eq_clipped
            hA hAB hBA hpA]
          rfl

/-- **Pointwise raw-survivor to Dirichlet-polarization weld.**

Let `a` be a clipped p-free survivor and `b` a p-divisible survivor in the
same first-owner/signature cell.  Returning `b` to the admitted parent
`b / p`, the raw #886 pair product is exactly the repository's signed
Dirichlet mixed-polarization atom.

This is the weight-preserving bridge into the existing signed owner telescope:
no norm, reciprocal factor, or ownerwise estimate is introduced. -/
theorem vfMidSurvivorPair_eq_dirichletPolarizationAtom
    {A B p a b : ℕ} {sig : Finset ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hp : p.Prime)
    (haCar : a ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (hbCar : b ∈ vfMidDyadicPrefixSurvivorCarrier A B)
    (haClip : a ∈ lowOwnerFirstOwnerClippedBaseFiber B p sig)
    (hbChild : b ∈ lowOwnerFirstOwnerChildFiber B p sig) :
    vfMidDyadicPrefixSurvivorSignedSite A B a *
        vfMidDyadicPrefixSurvivorSignedSite A B b =
      lowOwnerFirstOwnerDirichletPolarizationAtom B p (a, b / p) := by
  have hcAdm :
      b / p ∈ lowOwnerFirstOwnerAdmittedBaseFiber B p sig :=
    lowOwnerFirstOwner_div_mem_admitted_of_child hp hbChild
  have haBase := (Finset.mem_filter.mp haClip).1
  have haClock := (Finset.mem_filter.mp haBase).1
  have haIcc := (Finset.mem_filter.mp haClock).1
  have haX : a ≤ squareRootEndpoint B :=
    (Finset.mem_Icc.mp haIcc).2
  have hbaseSite :
      lowOwnerFirstOwnerDirichletBaseSite B a =
        realMoebiusStep a := by
    unfold lowOwnerFirstOwnerDirichletBaseSite
    rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le haX]
    rw [lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
      hA hAB hBA haCar]
    ring
  have hbDvd : p ∣ b :=
    (Finset.mem_filter.mp hbChild).2.2
  have hcancel : p * (b / p) = b :=
    Nat.mul_div_cancel' hbDvd
  have hretSite :
      lowOwnerFirstOwnerDirichletReturnedChildSite B p (b / p) =
        realMoebiusStep (b / p) := by
    rw [lowOwnerFirstOwnerDirichletReturnedChildSite_eq_returned_of_admitted
      hcAdm]
    rw [hcancel]
    rw [lowOwnerZeroFrequencyMobiusWeight_eq_one_on_vfMidSurvivor
      hA hAB hBA hbCar]
    ring
  have hcBase := (Finset.mem_filter.mp hcAdm).1
  have hpc : ¬ p ∣ b / p :=
    (Finset.mem_filter.mp hcBase).2.2
  have hmu :
      realMoebiusStep b = -realMoebiusStep (b / p) := by
    calc
      realMoebiusStep b =
          realMoebiusStep (p * (b / p)) := by rw [hcancel]
      _ = -realMoebiusStep (b / p) :=
        realMoebiusStep_mul_prime_eq_neg hp hpc
  have hatom :=
    lowOwnerFirstOwnerDirichletPolarizationAtom_eq_clipped_left
      haClip hcAdm
  calc
    vfMidDyadicPrefixSurvivorSignedSite A B a *
        vfMidDyadicPrefixSurvivorSignedSite A B b =
      realMoebiusStep a * realMoebiusStep b := by
        simp [vfMidDyadicPrefixSurvivorSignedSite, haCar, hbCar]
    _ = -(realMoebiusStep a * realMoebiusStep (b / p)) := by
        rw [hmu]
        ring
    _ = lowOwnerFirstOwnerDirichletPolarizationAtom B p (a, b / p) := by
        rw [hatom, hbaseSite, hretSite]
        ring


/-- **Global raw clipped entrance.**

After removing the diagonal, the complete #885/#886 survivor square is a sum
only of clipped-base x restricted-child first-owner cells with live owners
strictly above the frozen cutoff. -/
theorem vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveClippedCells
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSurvivorMobiusMassReal A B ^ 2 =
      lowOwnerGlobalDiagonalPairMassWith B
          (vfMidDyadicPrefixSurvivorSignedSite A B) +
        ∑ p ∈ vfMidDyadicPrefixSurvivorLiveFirstOwners A B,
          2 * ∑ sig ∈ lowOwnerFirstOwnerSignatureSet B p,
            (vfMidSurvivorClippedBaseAmplitude A B p sig *
              vfMidSurvivorChildAmplitude A B p sig) := by
  rw [vfMidDyadicPrefixSurvivorMobiusMass_sq_eq_diagonal_add_liveFirstOwners
    hA hAB hBA]
  apply congrArg
    (fun x : ℝ =>
      lowOwnerGlobalDiagonalPairMassWith B
        (vfMidDyadicPrefixSurvivorSignedSite A B) + x)
  apply Finset.sum_congr rfl
  intro p hp
  have hpA : A < p :=
    (Finset.mem_filter.mp hp).2
  have hpPrime : p.Prime :=
    (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  rw [lowOwnerGlobalFirstOwnerPairMassWith_eq_two_sum_cells
      hpPrime (vfMidDyadicPrefixSurvivorSignedSite A B)]
  congr 1
  apply Finset.sum_congr rfl
  intro sig _hsig
  rw [lowOwnerFirstOwnerCellGramWith_vfMidSurvivor_eq_clipped_mul_child
    hA hAB hBA hpA]

end RHLean.Analysis
