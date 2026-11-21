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

/-- These distinct sources are genuinely ANCESTRAL:
their physical Chebyshev error arguments lie between the owner prime
and the prior root R, not at the artificial constant quotient 1. -/
theorem alpogeDistinctResponseQuotient_ancestral
    (R p : ℕ) (hR : 4 ≤ R)
    (hp : alpogeDistinctResponsePrimeBand R p) :
    p ≤ alpogeDistinctResponseQuotient R p ∧
      alpogeDistinctResponseQuotient R p < R := by
  have hden : 0 < 2 * p := by
    have hp2 : 2 < p := hp.2.1
    omega
  have hNp := alpogeDistinctResponse_product_le_square R p hR hp
  have hRp : R ≤ 2 * p := hp.2.2.1
  constructor
  · unfold alpogeDistinctResponseQuotient
    apply (Nat.le_div_iff_mul_le hden).2
    nlinarith [hNp]
  · unfold alpogeDistinctResponseQuotient
    apply (Nat.div_lt_iff_lt_mul hden).2
    have hm : R * R ≤ R * (2 * p) := Nat.mul_le_mul_left R hRp
    have hsq : 1 ≤ R ^ 2 := by nlinarith
    have hlt : R ^ 2 - 1 < R ^ 2 := by omega
    calc
      R ^ 2 - 1 < R ^ 2 := hlt
      _ = R * R := by ring
      _ ≤ R * (2 * p) := hm

/-- Every selected K2 carrier 2*p is physically <= X_R=R²-1,
so it can be removed and returned within the COMPLETE original K2 sum. -/
theorem alpogeDistinctResponse_carrier_physical
    (R p : ℕ) (hR : 4 ≤ R)
    (hp : alpogeDistinctResponsePrimeBand R p) :
    2 * p ≤ R ^ 2 - 1 := by
  have hN := alpogeDistinctResponse_product_le_square R p hR hp
  have hp1 : 1 ≤ p := by
    have hp2 : 2 < p := hp.2.1
    omega
  have hle : 2 * p ≤ (2 * p) * p := by
    simpa using Nat.mul_le_mul_left (2 * p) hp1
  nlinarith [hle, hN]

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


/-- All carriers of the genuine near-root prime family actually lie in
the original signed second-Selberg summation range [1, R²-1]. -/
theorem alpogeDistinctResponseSiteSet_subset
    (R : ℕ) (P : Finset ℕ) (hR : 4 ≤ R)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    alpogeDistinctResponseSiteSet P ⊆ Finset.Icc 1 (R ^ 2 - 1) := by
  classical
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨p, hpP, hpn⟩
  subst n
  have hp := hP p hpP
  have hcarrier := alpogeDistinctResponse_carrier_physical R p hR hp
  have hp2 : 2 < p := hp.2.1
  exact Finset.mem_Icc.mpr ⟨by omega, hcarrier⟩

/-- Full signed complementary K2 source, with EVERY non-selected
prime square, prime power, off-band product and integer quotient retained. -/
def alpogeDistinctResponseOtherSource (R : ℕ) (P : Finset ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 (R ^ 2 - 1)).filter
      (fun n => n ∉ alpogeDistinctResponseSiteSet P),
    nativePNTSignedSecondSelbergKernel n *
      nativePNTError ((R ^ 2 - 1) / n)

/-- Exact finite partition of ALL K2*E terms into the DISTINCT
ancestral responses and the FULL signed complement. -/
theorem alpogeDistinctResponseK2_mass_partition
    (R : ℕ) (P : Finset ℕ) (hR : 4 ≤ R)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    nativePNTSignedSecondSelbergKernelErrorMass (R ^ 2 - 1) =
      alpogeDistinctResponseSource R P +
        alpogeDistinctResponseOtherSource R P := by
  classical
  have hsub := alpogeDistinctResponseSiteSet_subset R P hR hP
  have hfilter :
      (Finset.Icc 1 (R ^ 2 - 1)).filter
        (fun n => n ∈ alpogeDistinctResponseSiteSet P) =
      alpogeDistinctResponseSiteSet P := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · intro hn
      exact hn.2
    · intro hn
      exact ⟨hsub hn, hn⟩
  have hpart := (Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 (R ^ 2 - 1))
    (p := fun n => n ∈ alpogeDistinctResponseSiteSet P)
    (f := fun n => nativePNTSignedSecondSelbergKernel n *
      nativePNTError ((R ^ 2 - 1) / n))).symm
  unfold nativePNTSignedSecondSelbergKernelErrorMass
    alpogeDistinctResponseSource alpogeDistinctResponseOtherSource
  simpa only [hfilter] using hpart

/-- COMPLETE signed Selberg recurrence, now with an ACTUAL family of
distinct prior-scale Chebyshev error arguments and every off-family
term returned with its sign. No power estimate is assumed. -/
theorem alpogeDistinctResponseCompleteSignedSelberg
    (R : ℕ) (P : Finset ℕ) (hR : 4 ≤ R)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    nativePNTError (R ^ 2 - 1) *
        (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder (R ^ 2 - 1) *
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass (R ^ 2 - 1) +
        (∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
          nativePNTError (alpogeDistinctResponseQuotient R p)) +
        alpogeDistinctResponseOtherSource R P -
        nativePNTLambdaFloorLogSignedDefectMass (R ^ 2 - 1) := by
  have h := nativePNTError_mul_log_sq_eq_signedSecondSelberg (R ^ 2 - 1)
  rw [alpogeDistinctResponseK2_mass_partition R P hR hP,
    alpogeDistinctResponseSource_eq_prime_sum R P hP] at h
  linear_combination h


/-- Literal native copy of Alpoge Gz at any NATURAL endpoint; this is
proved equivalent to the external source formula in independent PR #1162.
Research modules must retain separate native-only import closures. -/
def alpogeDistinctNativeGzInteger (N : ℕ) : ℝ :=
  (N : ℝ) * nativeLambdaRecip N - nativePsi N -
    (N : ℝ) * Real.log (N : ℝ) +
    (1 + Real.eulerMascheroniConstant) * (N : ℝ)

/-- Exact arithmetic transport of a CHILD Chebyshev error into the
same-scale Alpoge Gz and reciprocal-Lambda channel. -/
theorem alpogeDistinctNativeError_eq_reciprocal_sub_Gz (N : ℕ) :
    nativePNTError N =
      (N : ℝ) *
        (nativeLambdaRecip N - Real.log (N : ℝ) +
          Real.eulerMascheroniConstant) -
        alpogeDistinctNativeGzInteger N := by
  unfold alpogeDistinctNativeGzInteger nativePNTError
  ring

/-- The FULL selected K2 family now becomes a genuine recursive Gz
input at DIFFERENT ancestral arguments t_p satisfying p<=t_p<R.
The complete K2 complement and original Selberg remainder stay intact. -/
theorem alpogeDistinctResponseCompleteSignedSelberg_Gz
    (R : ℕ) (P : Finset ℕ) (hR : 4 ≤ R)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    nativePNTError (R ^ 2 - 1) *
        (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 =
      nativePNTSignedSelbergRemainder (R ^ 2 - 1) *
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass (R ^ 2 - 1) +
        (∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
          ((alpogeDistinctResponseQuotient R p : ℝ) *
            (nativeLambdaRecip (alpogeDistinctResponseQuotient R p) -
              Real.log (alpogeDistinctResponseQuotient R p : ℝ) +
              Real.eulerMascheroniConstant) -
            alpogeDistinctNativeGzInteger (alpogeDistinctResponseQuotient R p))) +
        alpogeDistinctResponseOtherSource R P -
        nativePNTLambdaFloorLogSignedDefectMass (R ^ 2 - 1) := by
  have hsum :
      (∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
        nativePNTError (alpogeDistinctResponseQuotient R p)) =
      (∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
        ((alpogeDistinctResponseQuotient R p : ℝ) *
          (nativeLambdaRecip (alpogeDistinctResponseQuotient R p) -
            Real.log (alpogeDistinctResponseQuotient R p : ℝ) +
            Real.eulerMascheroniConstant) -
          alpogeDistinctNativeGzInteger (alpogeDistinctResponseQuotient R p))) := by
    apply Finset.sum_congr rfl
    intro p _hp
    rw [alpogeDistinctNativeError_eq_reciprocal_sub_Gz]
  rw [← hsum]
  exact alpogeDistinctResponseCompleteSignedSelberg R P hR hP

/-- An EXACT, source-faithful square-to-root functional recursion for
Alpoge's Gz: the parent Gz(R²-1) is expressed via the signed finite
sum of distinct Gz(t_p) at t_p<R, the reciprocal-Lambda terms, and
ALL remaining original signed Selberg contributions.

This is an identity, NOT a contraction estimate. The complementary
source and arithmetic-geometric cost are still outstanding. -/
theorem alpogeDistinctNativeGzSquareRecursion
    (R : ℕ) (P : Finset ℕ) (hR : 4 ≤ R)
    (hP : ∀ p ∈ P, alpogeDistinctResponsePrimeBand R p) :
    alpogeDistinctNativeGzInteger (R ^ 2 - 1) *
        (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 =
      ((R ^ 2 - 1 : ℕ) : ℝ) *
        (nativeLambdaRecip (R ^ 2 - 1) -
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) +
          Real.eulerMascheroniConstant) *
        (Real.log ((R ^ 2 - 1 : ℕ) : ℝ)) ^ 2 -
      (nativePNTSignedSelbergRemainder (R ^ 2 - 1) *
          Real.log ((R ^ 2 - 1 : ℕ) : ℝ) -
        nativePNTLambdaSignedSelbergRemainderMass (R ^ 2 - 1) +
        (∑ p ∈ P, 2 * Real.log (2 : ℝ) * Real.log (p : ℝ) *
          ((alpogeDistinctResponseQuotient R p : ℝ) *
            (nativeLambdaRecip (alpogeDistinctResponseQuotient R p) -
              Real.log (alpogeDistinctResponseQuotient R p : ℝ) +
              Real.eulerMascheroniConstant) -
            alpogeDistinctNativeGzInteger (alpogeDistinctResponseQuotient R p))) +
        alpogeDistinctResponseOtherSource R P -
        nativePNTLambdaFloorLogSignedDefectMass (R ^ 2 - 1)) := by
  have herror := alpogeDistinctResponseCompleteSignedSelberg_Gz R P hR hP
  have hG :
      alpogeDistinctNativeGzInteger (R ^ 2 - 1) =
        ((R ^ 2 - 1 : ℕ) : ℝ) *
          (nativeLambdaRecip (R ^ 2 - 1) -
            Real.log ((R ^ 2 - 1 : ℕ) : ℝ) +
            Real.eulerMascheroniConstant) -
        nativePNTError (R ^ 2 - 1) := by
    unfold alpogeDistinctNativeGzInteger nativePNTError
    ring
  rw [hG]
  linear_combination -herror

end RHLean.Analysis
