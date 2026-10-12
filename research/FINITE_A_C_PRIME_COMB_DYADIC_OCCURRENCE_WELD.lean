import Mathlib
import RHLean.Proof.DyadicSurvivorMertensInvariant

/-!
# Prime-comb chronological response = dyadic owner-two survivor, fibrewise

These are the SAME ACTUAL post-root prime sites, not a new model or a
conditional analytic estimate.

For a prime p > sqrt(W), the existing prime-comb one-step response is
  Delta_p(W) = 2 * (1 - M(floor(W/p))).
The existing surviving odd dyadic fibre is
  H_p(W) = -M(floor(W/p)).
Therefore
  Delta_p(W) = 2 * (1 + H_p(W)).
The global sum retains each genuine prime occurrence exactly once, including
the top half p > W/2, where Delta_p=0 and H_p=-1.

This weld is structural only. Neither the original live high-prime sector
nor the smooth sector is bounded by a signed anti-alignment theorem here.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

/-- Exact signed occurrence bridge: chronological prime-comb response and
the final dyadic surviving cofactor mass are the same lower Mertens packet,
with the explicit prime-seat normalization. -/
theorem primeCombTailSignedDelta_eq_two_plus_dyadicSurvivor
    {W p : ℕ} (hp : p.Prime)
    (hpRoot : Nat.sqrt W < p) (hpW : p ≤ W) :
    primeCombTailSignedDelta W p =
      2 * (1 + dyadicLargePrimeSurvivorMass W p) := by
  rw [primeCombTailSignedDelta_eq hp.pos hpW,
    dyadicLargePrimeSurvivorMass_eq_neg_mertens hp hpRoot]
  ring

/-- Each prime contributes once, even when the same historical quotient
appears for many distinct primes. No cofactor-owner de-duplication occurs. -/
def primeCombPostRootSignedDeltaTotal (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then primeCombTailSignedDelta W p else 0

/-- The integer number of actual post-root prime coordinates, embedded in
the same complex-valued currency as the physical signed prime comb. -/
def primeCombPostRootPrimeNumber (W : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ioc (Nat.sqrt W) W,
    if p.Prime then 1 else 0

/-- Global pre-absolute-value weld: the entire chronological response is
twice (the actual number of prime coordinates + the true surviving dyadic
high-prime mass). Cancellation within the signed survivor term is retained.
This identity is not a uniform finite-A estimate. -/
theorem primeCombPostRootSignedDeltaTotal_eq_primeNumber_add_dyadicSurvivor
    (W : ℕ) :
    primeCombPostRootSignedDeltaTotal W =
      2 * (primeCombPostRootPrimeNumber W +
        dyadicPostRootSurvivorMass W) := by
  unfold primeCombPostRootSignedDeltaTotal
    primeCombPostRootPrimeNumber dyadicPostRootSurvivorMass
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpRange
  by_cases hp : p.Prime
  · have hpRoot : Nat.sqrt W < p := (Finset.mem_Ioc.mp hpRange).1
    have hpW : p ≤ W := (Finset.mem_Ioc.mp hpRange).2
    simp only [hp, if_true]
    rw [primeCombTailSignedDelta_eq_two_plus_dyadicSurvivor hp hpRoot hpW]
    ring
  · simp [hp]

end RHLean.Proof
