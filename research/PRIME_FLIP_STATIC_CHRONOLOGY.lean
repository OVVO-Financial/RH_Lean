import Mathlib
import RHLean.Proof.PrimeCombVisualizationFrames
import RHLean.Proof.PrimeCombReciprocalBandCancellation
import «research.PRIME_FLIP_PNT_TELESCOPE»

/-!
# Arbitrary-snapshot chronology of the post-square-root prime comb

The chronological prime process does not have to be replayed at an arbitrary
endpoint `W`.  Once every prime through `sqrt W` has acted, the chronology is
encoded statically in each surviving factorization.

For every upper prime `p > sqrt W` and every admissible seat `c*p <= W`:

* the cofactor is already below the root, `c <= sqrt W`;
* on squarefree support the root frame literally stores the completed value
  `mu(c)`;
* the fresh upper owner changes the final value to `-mu(c)`;
* two distinct upper primes cannot own the same physical site;
* primes above `W/2` have no proper-multiple action and zero score increment.

The entire late chronology can therefore be read from the endpoint snapshot,
grouped by the reciprocal quotient `d = floor(W/p)`, and only the prime
multiplicity in each group is then replaced by Li/PNT density.  The inherited
Mobius response remains exact.

No estimate, asymptotic assumption, or RH hypothesis occurs in this module.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic
open RHLean.Proof

/-- Two distinct primes above the square-root frontier cannot divide the same
positive site below the endpoint.  Thus an upper-prime owner is unique in the
static endpoint snapshot. -/
theorem primeFlipSnapshot_postRootOwner_unique
    {W n p q : ℕ}
    (hnpos : 0 < n) (hnW : n ≤ W)
    (hp : p.Prime) (hq : q.Prime)
    (hpRoot : Nat.sqrt W < p) (hqRoot : Nat.sqrt W < q)
    (hpdiv : p ∣ n) (hqdiv : q ∣ n) :
    p = q := by
  by_contra hpq
  have hcop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpdq
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpdq)
  have hpqdvd : p * q ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hpdiv hqdiv
  have hpqle : p * q ≤ n := Nat.le_of_dvd hnpos hpqdvd
  have hpSucc : Nat.sqrt W + 1 ≤ p := by omega
  have hqSucc : Nat.sqrt W + 1 ≤ q := by omega
  have hsquare :
      (Nat.sqrt W + 1) * (Nat.sqrt W + 1) ≤ p * q :=
    Nat.mul_le_mul hpSucc hqSucc
  have hWlt : W < (Nat.sqrt W + 1) ^ 2 := Nat.lt_succ_sqrt' W
  have hWlt' : W < (Nat.sqrt W + 1) * (Nat.sqrt W + 1) := by
    simpa [pow_two] using hWlt
  omega

/-- **Static chronology theorem.**  At any endpoint, a squarefree late seat
`c*p` with `p > sqrt W` already carries the completed lower-cofactor value
after the root phase, and the unique fresh owner reverses exactly that value. -/
theorem primeFlipSnapshot_tailSeat_chronology
    {W c p : ℕ}
    (hp : p.Prime) (hpRoot : Nat.sqrt W < p)
    (hc : 2 ≤ c) (hcpW : c * p ≤ W)
    (hsq : Squarefree (c * p)) :
    c ≤ Nat.sqrt W ∧
      primeCombFrameSite (primesUpTo (Nat.sqrt W)) (c * p) = μ c ∧
      canonicalMoebiusWeight (c * p) = -canonicalMoebiusWeight c := by
  refine ⟨cofactor_le_sqrt_of_largePrime_mul_le hpRoot hcpW, ?_, ?_⟩
  · exact primeCombSqrtFrame_tailSeat_eq_cofactorMoebius
      hp hpRoot hc hcpW hsq
  · exact canonicalMoebiusWeight_mul_largePrime_eq_neg_cofactor
      hp hpRoot (by omega) hcpW

private theorem primeFlipSnapshot_mertens_one :
    mertensSummatory 1 = 1 := by
  rw [← cofactorMobiusPrefixMass_eq_mertensSummatory]
  simp [cofactorMobiusPrefixMass, canonicalMoebiusWeight]

/-- The top-half primes are chronologically inert: they have no proper
multiple and their displayed late-prime score increment is exactly zero. -/
theorem primeFlipSnapshot_topHalf_inert
    {W p : ℕ} (hp : p.Prime)
    (hpHalf : W / 2 < p) (hpW : p ≤ W) :
    primeCombProperMultiplierSet p W = ∅ ∧
      primeCombTailSignedDelta W p = 0 := by
  constructor
  · exact primeCombProperMultiplierSet_eq_empty_of_half_lt hp.pos hpHalf
  · have hlo : 1 * p ≤ W := by simpa using hpW
    have hhi : W < (1 + 1) * p := by
      have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).1 hpHalf
      simpa [Nat.mul_comm] using h
    have hdiv : W / p = 1 := Nat.div_eq_of_lt_le hlo hhi
    rw [primeCombTailSignedDelta_eq hp.pos hpW, hdiv,
      primeFlipSnapshot_mertens_one]
    ring

/-- Literal chronological late correction read from the final endpoint:
sum the exact prime-comb score changes of all owners above `sqrt W`. -/
def primeFlipSnapshotLateCorrection (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then primeCombTailSignedDelta W p else 0

/-- The static chronological correction is exactly twice the inherited-response
operator used by the PNT comparison layer. -/
theorem primeFlipSnapshotLateCorrection_eq_two_exactResponse
    (W : ℕ) :
    primeFlipSnapshotLateCorrection W =
      2 * primeFlipExactResponse (Nat.sqrt W) W := by
  classical
  unfold primeFlipSnapshotLateCorrection primeFlipExactResponse
  calc
    (∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
        if p.Prime then primeCombTailSignedDelta W p else 0) =
      ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
        2 * (primeSievePrimeIndicator p *
          primeFlipInheritedResponse (W / p)) := by
      apply Finset.sum_congr rfl
      intro p hpRange
      have hpW : p ≤ W := (Finset.mem_Ioc.mp hpRange).2
      by_cases hpPrime : p.Prime
      · rw [if_pos hpPrime, primeCombTailSignedDelta_eq hpPrime.pos hpW]
        simp [primeSievePrimeIndicator, primeFlipInheritedResponse, hpPrime]
      · simp [primeSievePrimeIndicator, hpPrime]
    _ = 2 * ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
        primeSievePrimeIndicator p *
          primeFlipInheritedResponse (W / p) := by
      rw [Finset.mul_sum]

/-- Compressing the already-completed chronology by reciprocal quotient loses
nothing: each band is its exact prime multiplicity times one inherited lower
Mertens response. -/
theorem primeFlipSnapshotLateCorrection_eq_reciprocalBands
    (W : ℕ) :
    primeFlipSnapshotLateCorrection W =
      2 * ∑ d ∈ primeSieveQuotientSupport (Nat.sqrt W) W,
        primeSieveReciprocalPrimeCount (Nat.sqrt W) W d *
          primeFlipInheritedResponse d := by
  rw [primeFlipSnapshotLateCorrection_eq_two_exactResponse,
    primeFlipExactResponse_eq_reciprocalPrimeCounts]

/-- Every inherited quotient exposed by an upper prime is itself at or below
the square-root frontier.  The late stage therefore only copies already
completed lower-prefix data. -/
theorem primeFlipSnapshot_quotientTop_le_root
    (W : ℕ) :
    W / (Nat.sqrt W + 1) ≤ Nat.sqrt W := by
  have hlt : W < (Nat.sqrt W + 1) ^ 2 := Nat.lt_succ_sqrt' W
  have hlt' : W < (Nat.sqrt W + 1) * (Nat.sqrt W + 1) := by
    simpa [pow_two] using hlt
  have hdiv :
      W / (Nat.sqrt W + 1) < Nat.sqrt W + 1 :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).2 hlt'
  omega

/-- **PNT acts only on multiplicity.**  The exact chronological endpoint
correction equals the Li/PNT multiplicity model plus the signed prime-location
error, while the inherited Möbius response is untouched. -/
theorem primeFlipSnapshotLateCorrection_eq_two_pnt_add_error
    (W : ℕ) :
    primeFlipSnapshotLateCorrection W =
      2 * primeFlipPNTResponse (Nat.sqrt W) W +
        2 * primeFlipPNTError (Nat.sqrt W) W := by
  rw [primeFlipSnapshotLateCorrection_eq_two_exactResponse,
    primeFlipExactResponse_eq_pnt_add_error]
  ring

/-- At every nontrivial arbitrary endpoint, the multiplicity-replacement error
atomizes after Abel summation: the interior Mertens-prefix coefficients collapse
to individual Möbius atoms, plus one root boundary term. -/
theorem primeFlipSnapshotPNTError_eq_moebiusAtoms
    {W : ℕ} (hW : 2 ≤ W) :
    primeFlipPNTError (Nat.sqrt W) W =
      -(∑ d ∈ Finset.Icc 2 (W / (Nat.sqrt W + 1)),
          (((μ d : ℤ) : ℂ)) * primeSievePrimeDiscrepancy (W / d)) +
        (mertensSummatory (W / (Nat.sqrt W + 1)) - 1) *
          primeSievePrimeDiscrepancy (Nat.sqrt W) := by
  have hsle : Nat.sqrt W ≤ W := Nat.sqrt_le_self W
  have hslt : Nat.sqrt W < W := by
    by_contra hnot
    have heq : Nat.sqrt W = W :=
      Nat.le_antisymm hsle (Nat.le_of_not_gt hnot)
    have hsquare : (Nat.sqrt W) ^ 2 ≤ W := Nat.sqrt_le' W
    rw [heq] at hsquare
    nlinarith
  have hstep : Nat.sqrt W + 1 ≤ W := by omega
  exact primeFlipPNTError_eq_moebiusAtoms hsle hstep

end RHLean.Analysis
