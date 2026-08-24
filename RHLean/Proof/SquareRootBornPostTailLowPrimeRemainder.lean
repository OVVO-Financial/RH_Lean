import Mathlib
import RHLean.Proof.SquareRootBornPostTailLowPrimeCollapse

/-!
# Near-root remainder after the BornPostTail low-prime cutoff

This module continues the exact cofactor-response reduction from
`SquareRootBornPostTailLowPrimeCollapse`.

Write

`P_R = R - floor(sqrt R)`.

After the low-prime coordinates through `P_R` have been separated, the born
complement vanishes exactly.  On the post-root side, every remaining cofactor
with largest prime factor above `P_R` is itself a prime in `(P_R,R)`.  There are
at most `sqrt R` such cofactor seats, and every one sees at most `2 sqrt R`
post-root prime seats.  Because every surviving cofactor is prime, its Mobius
weight is exactly `-1`; the boundary remainder is therefore a positive natural
cardinality, not a triangle-inequality estimate.

The resulting bound is the elementary finite estimate

`||nearRootRemainder|| <= 2 R`.

No PNT estimate, RH hypothesis, density model, independence assumption, or
Mertens bound occurs.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

private theorem two_mul_canonicalLargestPrimeFactor_le_of_lt
    {c : ℕ} (hc : 1 < c)
    (hlt : canonicalLargestPrimeFactor c < c) :
    2 * canonicalLargestPrimeFactor c ≤ c := by
  have hdvd := canonicalLargestPrimeFactor_dvd hc
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hk0', mul_zero] at hk
    omega
  have hkone : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one] at hk
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  simpa [Nat.mul_comm] using
    (Nat.mul_le_mul_left (canonicalLargestPrimeFactor c) hk2)

/-- If the largest prime factor of a cofactor lies beyond the low-prime cutoff,
that cofactor has no born-smooth partner at all.  This is exact vanishing, not
a smallness estimate. -/
theorem squareRootBornPartnerCount_eq_zero_of_lowPrimeCutoff_lt_lpf
    {R c : ℕ} (hR : 16 ≤ R)
    (hcP : squareRootBornPostTailLowPrimeCutoff R <
      canonicalLargestPrimeFactor c) :
    squareRootBornPartnerCount R c = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  rw [squareRootBornPartnerSet, Finset.mem_filter] at hq
  obtain ⟨hqRange, hqPrime, hpq, hqc, hcqX⟩ := hq
  have hcgt : 1 < c := lt_of_lt_of_le hqPrime.one_lt hqc
  have hpc : canonicalLargestPrimeFactor c < c := hpq.trans_le hqc
  have h2p : 2 * canonicalLargestPrimeFactor c ≤ c :=
    two_mul_canonicalLargestPrimeFactor_le_of_lt hcgt hpc
  have hPq : squareRootBornPostTailLowPrimeCutoff R < q := hcP.trans hpq
  have hlow :
      2 * (squareRootBornPostTailLowPrimeCutoff R) ^ 2 < c * q := by
    nlinarith
  have hgeom := squareRootBornPostTailLowPrimeCutoff_two_sq_gt_endpoint hR
  omega

/-- Cofactors in the high response whose largest prime coordinate has not yet
been processed at `P_R`. -/
def squareRootBornPostTailHighComplementCofactors (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (R - 1)).filter fun c =>
    squareRootBornPostTailLowPrimeCutoff R < canonicalLargestPrimeFactor c

@[simp] theorem mem_squareRootBornPostTailHighComplementCofactors
    {R c : ℕ} :
    c ∈ squareRootBornPostTailHighComplementCofactors R ↔
      1 ≤ c ∧ c ≤ R - 1 ∧
        squareRootBornPostTailLowPrimeCutoff R <
          canonicalLargestPrimeFactor c := by
  simp [squareRootBornPostTailHighComplementCofactors]

/-- High-complement rigidity: above `P_R`, a cofactor below `R` cannot retain a
proper largest-prime-factor quotient.  It is itself prime, and lies in the
near-root interval `(P_R,R)`. -/
theorem squareRootBornPostTailHighComplement_prime
    {R c : ℕ} (hR : 16 ≤ R)
    (hc : c ∈ squareRootBornPostTailHighComplementCofactors R) :
    c.Prime ∧ squareRootBornPostTailLowPrimeCutoff R < c ∧ c < R := by
  rcases mem_squareRootBornPostTailHighComplementCofactors.mp hc with
    ⟨hc1, hcR, hcP⟩
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hRP : R < 2 * P := by
    simpa [P] using squareRootBornPostTailLowPrimeCutoff_two_mul_gt_root hR
  have hP1 : 1 < P := by omega
  have hcgt : 1 < c := by
    by_contra h
    have hcnot : ¬ 1 < c := by omega
    have hlpf : canonicalLargestPrimeFactor c = 1 := by
      simp [canonicalLargestPrimeFactor, hcnot]
    rw [hlpf] at hcP
    omega
  have hpPrime := canonicalLargestPrimeFactor_prime hcgt
  have hpDvd := canonicalLargestPrimeFactor_dvd hcgt
  have hpLeC : canonicalLargestPrimeFactor c ≤ c :=
    Nat.le_of_dvd (by omega) hpDvd
  have hpEq : canonicalLargestPrimeFactor c = c := by
    apply le_antisymm hpLeC
    by_contra hcp
    have hpLtC : canonicalLargestPrimeFactor c < c := by omega
    have h2p : 2 * canonicalLargestPrimeFactor c ≤ c :=
      two_mul_canonicalLargestPrimeFactor_le_of_lt hcgt hpLtC
    have hPp : P < canonicalLargestPrimeFactor c := by simpa [P] using hcP
    have hR2p : R < 2 * canonicalLargestPrimeFactor c := by omega
    omega
  have hcPrime : c.Prime := by simpa [hpEq] using hpPrime
  exact ⟨hcPrime, by simpa [hpEq] using hcP, by omega⟩

private theorem remainder_sqrt_ge_four_of_sixteen_le
    {R : ℕ} (hR : 16 ≤ R) : 4 ≤ Nat.sqrt R := by
  by_contra h
  have hs : Nat.sqrt R ≤ 3 := by omega
  have hlt := Nat.lt_succ_sqrt' R
  have hsq : (Nat.sqrt R + 1) ^ 2 ≤ 16 := by nlinarith
  nlinarith

private theorem remainder_four_mul_sqrt_le
    {R : ℕ} (hR : 16 ≤ R) : 4 * Nat.sqrt R ≤ R := by
  have hs4 := remainder_sqrt_ge_four_of_sixteen_le hR
  have hsquare : (Nat.sqrt R) ^ 2 ≤ R := Nat.sqrt_le' R
  nlinarith

/-- The reciprocal cutoff of every unprocessed cofactor is at most
`R + 2 floor(sqrt R)`. -/
theorem squareRootBornPostTail_reciprocalCutoff_le_root_add_two_sqrt
    {R d : ℕ} (hR : 16 ≤ R)
    (hdP : squareRootBornPostTailLowPrimeCutoff R < d) :
    squareRootEndpoint R / d ≤ R + 2 * Nat.sqrt R := by
  let s := Nat.sqrt R
  let P := squareRootBornPostTailLowPrimeCutoff R
  have hs4 : 4 ≤ s := by
    simpa [s] using remainder_sqrt_ge_four_of_sixteen_le hR
  have h4s : 4 * s ≤ R := by
    simpa [s] using remainder_four_mul_sqrt_le hR
  have hsR : s ≤ R := by nlinarith [Nat.sqrt_le' R]
  have hPs : P + s = R := by
    dsimp [P, squareRootBornPostTailLowPrimeCutoff, s]
    omega
  have hd : P + 1 ≤ d := by simpa [P] using hdP
  have hbase : R ^ 2 ≤ (R + 2 * s) * (P + 1) := by
    nlinarith [Nat.sqrt_le' R]
  have hmono : (R + 2 * s) * (P + 1) ≤ (R + 2 * s) * d :=
    Nat.mul_le_mul_left (R + 2 * s) hd
  have hX : squareRootEndpoint R ≤ (R + 2 * s) * d := by
    have hXR : squareRootEndpoint R < R ^ 2 := by
      unfold squareRootEndpoint
      exact Nat.sub_lt (by positivity) (by norm_num)
    exact (Nat.le_of_lt hXR).trans (hbase.trans hmono)
  have hdpos : 0 < d := by omega
  apply (Nat.div_le_iff_le_mul hdpos).2
  simpa [Nat.mul_comm] using hX

/-- Every post-root prefix seen by an unprocessed cofactor contains at most
`2 floor(sqrt R)` primes. -/
theorem squareRootPostRootPrimePrefixCard_le_two_sqrt_of_lowPrimeCutoff_lt
    {R d : ℕ} (hR : 16 ≤ R)
    (hdP : squareRootBornPostTailLowPrimeCutoff R < d) :
    squareRootPostRootPrimePrefixCard R d ≤ 2 * Nat.sqrt R := by
  classical
  let U := max R (squareRootEndpoint R / d)
  have hdiv :=
    squareRootBornPostTail_reciprocalCutoff_le_root_add_two_sqrt hR hdP
  have hU : U ≤ R + 2 * Nat.sqrt R := by
    dsimp [U]
    exact max_le (by omega) hdiv
  unfold squareRootPostRootPrimePrefixCard
  change ((Finset.Ioc R U).filter Nat.Prime).card ≤ 2 * Nat.sqrt R
  have hsub :
      (Finset.Ioc R U).filter Nat.Prime ⊆
        Finset.Ioc R (R + 2 * Nat.sqrt R) := by
    intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hqIoc, _⟩
    rcases Finset.mem_Ioc.mp hqIoc with ⟨hRq, hqU⟩
    exact Finset.mem_Ioc.mpr ⟨hRq, hqU.trans hU⟩
  have hcard := Finset.card_le_card hsub
  have hIoc :
      (Finset.Ioc R (R + 2 * Nat.sqrt R)).card = 2 * Nat.sqrt R := by
    rw [Nat.card_Ioc]
    omega
  simpa [hIoc] using hcard

/-- Natural Abel telescope: one reciprocal layer plus the deeper post-root
prefix is exactly the prefix at the current reciprocal depth. -/
theorem squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard
    (R K : ℕ) (hR : 1 ≤ R) (hK : 1 ≤ K) (hKR : K < R) :
    squareRootReciprocalPrimeLayerCard R K +
        squareRootPostRootPrimePrefixCard R (K + 1) =
      squareRootPostRootPrimePrefixCard R K := by
  have hC :
      ((squareRootReciprocalPrimeLayerCard R K : ℕ) : ℂ) =
        ((squareRootPostRootPrimePrefixCard R K : ℕ) : ℂ) -
          ((squareRootPostRootPrimePrefixCard R (K + 1) : ℕ) : ℂ) := by
    rw [squareRootPostRootPrimePrefixCard_cast,
      squareRootPostRootPrimePrefixCard_cast]
    rw [← squareRootReciprocalPrimeCount_eq_layerCard]
    exact squareRoot_reciprocalPrimeCount_eq_postRootPrefix_diff hR hK hKR
  have hsumC :
      (((squareRootReciprocalPrimeLayerCard R K +
          squareRootPostRootPrimePrefixCard R (K + 1) : ℕ)) : ℂ) =
        ((squareRootPostRootPrimePrefixCard R K : ℕ) : ℂ) := by
    push_cast
    linear_combination hC
  exact_mod_cast hsumC

/-- Pointwise near-root bound for the still-unprocessed high response.  The
partially filled crossing layer is kept together with every deeper layer, and
is bounded only after the exact natural Abel telescope above. -/
theorem squareRootBornPostTailHighResponse_le_two_sqrt
    {R K j c : ℕ} (hR : 16 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hcP : squareRootBornPostTailLowPrimeCutoff R < c) :
    squareRootBornPostTailHighResponse R K j c ≤ 2 * Nat.sqrt R := by
  unfold squareRootBornPostTailHighResponse
  by_cases hcK : c ≤ K
  · rw [if_pos hcK]
    have hPK : squareRootBornPostTailLowPrimeCutoff R < K :=
      hcP.trans_le hcK
    have hprefix :=
      squareRootPostRootPrimePrefixCard_le_two_sqrt_of_lowPrimeCutoff_lt
        hR hPK
    have htel :=
      squareRootReciprocalPrimeLayerCard_add_postRootPrimePrefixCard
        R K (by omega) hK hKR
    omega
  · rw [if_neg hcK]
    exact squareRootPostRootPrimePrefixCard_le_two_sqrt_of_lowPrimeCutoff_lt
      hR hcP

end RHLean.Proof
