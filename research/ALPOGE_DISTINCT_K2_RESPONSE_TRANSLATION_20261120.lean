import Mathlib
import RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier

/-!
# Noncollapsed physical K2 responses with near-root prime multiplicity

The old signed prime-band Schur matrix used p*q near X=R^2-1, so every
response was E(floor(X/(p*q)))=E(1). That is NOT independent arithmetic
response multiplicity.

Here the cofactor 2 is fixed while p ranges over genuine primes in
[R/2, 2R/3]. The kernel K2(2*p) has an EXACT factor two, and the
physical quotient t_p=floor((R^2-1)/(2*p)) is INJECTIVE on this band.
The distinct responses survive the actual source map without assumptions
on the signs of E(t_p).

Counting prime labels near R gives m~R/(6 log R) from classical PNT,
but this file does not formalize PNT's interval asymptotic. Nor does
the coefficient 2 imply the external automorphic Hecke covolume bound.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- Genuine near-root odd prime window. -/
def alpogeDistinctResponsePrimeBand (R p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧ R ≤ 2 * p ∧ 3 * p ≤ 2 * R

/-- The ACTUAL distinct reciprocal argument of the complete signed K2 source. -/
def alpogeDistinctResponseQuotient (R p : ℕ) : ℕ :=
  (R ^ 2 - 1) / (2 * p)

/-- Elementary source inequality: the cofactor quotient is at least the prime
owner, so its floor changes strictly as the owner increases. -/
theorem alpogeDistinctResponse_product_le_square
    (R q : ℕ) (hR : 4 ≤ R)
    (hq : alpogeDistinctResponsePrimeBand R q) :
    2 * q * q ≤ R ^ 2 - 1 := by
  have hbound : 3 * q ≤ 2 * R := hq.2.2.2
  have hsq : (3 * q) * (3 * q) ≤ (2 * R) * (2 * R) :=
    Nat.mul_self_le_mul_self hbound
  have hR2 : 9 ≤ R ^ 2 := by nlinarith
  have hadd : 2 * q * q + 1 ≤ R ^ 2 := by nlinarith [hsq, hR2]
  omega

/-- A strictly DECREASING, integer-valued reciprocal map, for any p<q
with a large enough square relative to q; no prime randomness is used. -/
theorem alpogeDistinctResponse_div_strict
    (N p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hN : 2 * q * q ≤ N) :
    N / (2 * q) < N / (2 * p) := by
  have hqpos : 0 < 2 * q := by omega
  have hppos : 0 < 2 * p := by omega
  have hqdiv : q ≤ N / (2 * q) := by
    apply (Nat.le_div_iff_mul_le hqpos).2
    nlinarith [hN]
  have hmul : (N / (2 * q)) * (p + 1) ≤ (N / (2 * q)) * q :=
    Nat.mul_le_mul_left _ (by omega)
  have hfloor : (N / (2 * q)) * (2 * q) ≤ N :=
    Nat.div_mul_le_self N (2 * q)
  have hplus : (N / (2 * q) + 1) * (2 * p) ≤ N := by
    nlinarith [hmul, hfloor, hqdiv]
  have hnext : N / (2 * q) + 1 ≤ N / (2 * p) :=
    (Nat.le_div_iff_mul_le hppos).2 hplus
  omega

/-- Crucial improvement over the old 2I-J quotient-one face:
distinct physical prime owners give DISTINCT actual E(t_p) arguments. -/
theorem alpogeDistinctResponseQuotient_injective
    (R p q : ℕ) (hR : 4 ≤ R)
    (hp : alpogeDistinctResponsePrimeBand R p)
    (hq : alpogeDistinctResponsePrimeBand R q)
    (heq : alpogeDistinctResponseQuotient R p =
      alpogeDistinctResponseQuotient R q) : p = q := by
  unfold alpogeDistinctResponseQuotient at heq
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · have hN := alpogeDistinctResponse_product_le_square R q hR hq
    have hstrict := alpogeDistinctResponse_div_strict (R ^ 2 - 1)
      p q hp.1.pos hpq hN
    omega
  · exact hpq
  · have hN := alpogeDistinctResponse_product_le_square R p hR hp
    have hstrict := alpogeDistinctResponse_div_strict (R ^ 2 - 1)
      q p hq.1.pos hqp hN
    omega

/-- Exact signed Selberg kernel on the selected distinct-prime carrier 2*p:
the factor of TWO is physical, not borrowed from a proxy matrix. -/
theorem alpogeDistinctResponse_K2_prime_two
    (R p : ℕ) (hp : alpogeDistinctResponsePrimeBand R p) :
    nativePNTSignedSecondSelbergKernel (2 * p) *
        nativePNTError (alpogeDistinctResponseQuotient R p) =
      2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
        nativePNTError (alpogeDistinctResponseQuotient R p) := by
  have hp2 : 2 < p := hp.2.1
  have hneq : 2 ≠ p := by omega
  rw [nativePNTSignedSecondSelbergKernel_mul_distinct_primes
    2 p Nat.prime_two hp.1 hneq]
  norm_num

/-- Physical selected carrier set for an arbitrary finite prime family. -/
def alpogeDistinctResponseSiteSet (P : Finset ℕ) : Finset ℕ :=
  P.image (fun p => 2 * p)

/-- Actual subset contribution of the COMPLETE signed second-Selberg kernel. -/
def alpogeDistinctResponseSource (R : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ n ∈ alpogeDistinctResponseSiteSet P,
    nativePNTSignedSecondSelbergKernel n *
      nativePNTError ((R ^ 2 - 1) / n)

/-- Source-faithful reindexing: each carrier 2*p is counted ONCE and samples
a genuinely distinct error argument on the prescribed prime band. -/
theorem alpogeDistinctResponseSource_eq_prime_sum
    (R : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    alpogeDistinctResponseSource R P =
      ∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
        nativePNTError (alpogeDistinctResponseQuotient R p) := by
  unfold alpogeDistinctResponseSource alpogeDistinctResponseSiteSet
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    simpa only [alpogeDistinctResponseQuotient] using
      alpogeDistinctResponse_K2_prime_two R p (hP p hp)
  · intro p _hp q _hq heq
    change 2 * p = 2 * q at heq
    omega

end RHLean.Analysis
