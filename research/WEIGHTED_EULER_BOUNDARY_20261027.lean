import Mathlib
import RHLean.Proof.PrimeCombVisualizationDynamics
import «research.GLOBAL_RETURNED_CORE_BOOLEAN_CARDINALITY_AUDIT»

/-!
# Weighted Euler boundary and two notions of first ownership

The least-prime factor of an integer is invariant when a larger prime is added.
The *first-separation* owner of a squarefree pair, used by the returned-core
Gram, is a different notion.  Moreover the actual common-clock AMP coefficient
is a sum of root and q^2-daughter cutoff indicators, not a function of the
integer's least-prime factor.

This file establishes the genuinely unrestricted finite weighted Euler step,
the least-prime invariance, and the precise cutoff-specialization.  The true
AMP coefficient retains the pre-existing daughter/root crossing difference.
A small genuine coefficient witness refutes zero-gradient transport.

No conditional mixed-tail estimate, exponent gain, or RH theorem is claimed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic

/-- The generic finite weighted Euler step. The selected vertices are
products of subsets of U, including the empty product 1. This statement
requires no prime-factor restrictions on U for the finite algebra. -/
theorem weightedEulerStep_eq_boundaryDefect
    {U : Finset ℕ} {p : ℕ} (hp : p ∉ U) (a : ℕ → ℝ) :
    (∑ t ∈ (insert p U).powerset,
       (-1 : ℝ) ^ t.card * a (primeFaceProduct t)) =
      ∑ t ∈ U.powerset,
        (-1 : ℝ) ^ t.card *
          (a (primeFaceProduct t) - a (p * primeFaceProduct t)) := by
  classical
  rw [Finset.sum_powerset_insert hp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : p ∉ t :=
    Finset.notMem_of_mem_powerset_of_notMem ht hp
  have hprod :
      primeFaceProduct (insert p t) = p * primeFaceProduct t := by
    simp [primeFaceProduct, hpt]
  rw [hprod, Finset.card_insert_of_notMem hpt, pow_succ]
  ring

/-- Multiplying a nontrivial integer by a prime larger than its least prime
factor preserves its least-prime factor.  Squarefreeness and freshness are
not required for this owner identity; freshness is needed separately for
the Mobius sign flip. -/
theorem firstOwner_mul_prime_of_gt
    {c p : ℕ} (hc : 1 < c) (hp : p.Prime)
    (hgt : Nat.minFac c < p) :
    Nat.minFac (p * c) = Nat.minFac c := by
  have hcne : c ≠ 1 := by omega
  have hqprime : (Nat.minFac c).Prime := Nat.minFac_prime hcne
  have hqdiv : Nat.minFac c ∣ c := Nat.minFac_dvd c
  have hqchild : Nat.minFac c ∣ p * c :=
    dvd_mul_of_dvd_right hqdiv p
  have hnewgt : 1 < p * c := by
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  have hnewne : p * c ≠ 1 := by omega
  have hrprime : (Nat.minFac (p * c)).Prime := Nat.minFac_prime hnewne
  have hrdiv : Nat.minFac (p * c) ∣ p * c := Nat.minFac_dvd (p * c)
  have hrle : Nat.minFac (p * c) ≤ Nat.minFac c :=
    Nat.minFac_le_of_dvd hqprime.two_le hqchild
  have hler : Nat.minFac c ≤ Nat.minFac (p * c) := by
    rcases hrprime.dvd_mul.mp hrdiv with hrp | hrc
    · have heq : Nat.minFac (p * c) = p :=
        (Nat.prime_dvd_prime_iff_eq hrprime hp).mp hrp
      omega
    · exact Nat.minFac_le_of_dvd hrprime.two_le hrc
  exact Nat.le_antisymm hrle hler

/-- A truly least-prime-owner-only weight has no interior shift. On a
downward-closed prefix its defect is confined to admitted parents with
children beyond the cutoff. This is NOT the original AMP weight. -/
theorem firstOwnerWeightedCutoff_pureBoundary
    {c p X : ℕ} (hc : 1 < c) (hp : p.Prime)
    (hgt : Nat.minFac c < p) (w : ℕ → ℝ) :
    (if c ≤ X then w (Nat.minFac c) else 0) -
        (if p * c ≤ X then w (Nat.minFac (p * c)) else 0) =
      if c ≤ X ∧ X < p * c then w (Nat.minFac c) else 0 := by
  rw [firstOwner_mul_prime_of_gt hc hp hgt]
  have hle : c ≤ p * c := by
    calc
      c = 1 * c := (one_mul c).symm
      _ ≤ p * c := Nat.mul_le_mul_right c hp.one_le
  by_cases hcX : c ≤ X
  · by_cases hpX : p * c ≤ X
    · simp [hcX, hpX, Nat.not_lt_of_ge hpX]
    · have hcross : X < p * c := Nat.lt_of_not_ge hpX
      simp [hcX, hpX, hcross]
  · have hpX : ¬ p * c ≤ X := by
      intro h
      exact hcX (hle.trans h)
    simp [hcX, hpX]

/-- The correct combination: least-prime ownership stays constant, but
the actual AMP coefficient has the *nonzero* physical daughter/root
crossing gradient proved by the returned-core source. -/
theorem firstOwnerInvariant_actualAMP_crossings
    {R c p : ℕ} (hc : 1 < c) (hp : p.Prime)
    (hgt : Nat.minFac c < p) :
    Nat.minFac (p * c) = Nat.minFac c ∧
      lowOwnerZeroFrequencyMobiusWeight R c -
          lowOwnerZeroFrequencyMobiusWeight R (p * c) =
        lowOwnerDaughterCrossingWeight R p c -
          lowOwnerRootCrossingIndicator R p c := by
  exact ⟨firstOwner_mul_prime_of_gt hc hp hgt,
    lowOwnerZeroFrequencyMobiusWeight_sub_mul hp.one_le⟩

/-- Physical falsifier to transporting the actual AMP weight as an
integer-first-owner-only scalar. At R=56 the low q^2 owners are {3,5,7};
the fresh insertion 3 -> 23*3 preserves least owner 3, but it crosses
the root and q=7 daughter thresholds. The weight difference is -6/7. -/
theorem actualAMPWeight_not_ownerOnly_56 :
    Nat.minFac (23 * 3) = Nat.minFac 3 ∧
      lowOwnerZeroFrequencyMobiusWeight 56 3 -
        lowOwnerZeroFrequencyMobiusWeight 56 (23 * 3) =
          -(6 / 7 : ℝ) := by
  have hmin : Nat.minFac (23 * 3) = Nat.minFac 3 :=
    firstOwner_mul_prime_of_gt (by norm_num)
      (by norm_num) (by norm_num)
  have h3 :
      lowOwnerReciprocalDaughterWeight 56 3 = (71 : ℝ) / 105 := by
    norm_num [lowOwnerReciprocalDaughterWeight,
      canonicalRoughLowQ2Owners_56, rawQ2ChildCutoff, squareRootEndpoint]
  have h69 :
      lowOwnerReciprocalDaughterWeight 56 (23 * 3) = (8 : ℝ) / 15 := by
    norm_num [lowOwnerReciprocalDaughterWeight,
      canonicalRoughLowQ2Owners_56, rawQ2ChildCutoff, squareRootEndpoint]
  refine ⟨hmin, ?_⟩
  unfold lowOwnerZeroFrequencyMobiusWeight
  rw [h3, h69]
  norm_num [lowOwnerFarTailWeight]

/-- A scale counterexample: a peeling prime p above a proposed threshold
does not place an unmatched parent into the corresponding short-cofactor
range. For q=3, p=13, m=385=5*7*11, R=56, the parent is admitted and its
child is excluded even though m exceeds X/(q*8). -/
theorem unmatchedParent_not_short_of_largePeelingPrime :
    (8 : ℕ) < 13 ∧
      (56 ^ 2 - 1) / (3 * 13) < 385 ∧
      385 ≤ (56 ^ 2 - 1) / 3 ∧
      (56 ^ 2 - 1) / (3 * 8) < 385 := by
  norm_num

#print axioms weightedEulerStep_eq_boundaryDefect
#print axioms firstOwner_mul_prime_of_gt
#print axioms firstOwnerWeightedCutoff_pureBoundary
#print axioms firstOwnerInvariant_actualAMP_crossings
#print axioms actualAMPWeight_not_ownerOnly_56
#print axioms unmatchedParent_not_short_of_largePeelingPrime

end RHLean.Proof
