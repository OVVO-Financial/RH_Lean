import Mathlib
import RHLean.Arithmetic.PrimeWheelMobiusRecovery
import «research.GLOBAL_RETURNED_CORE_FINAL_STOKES_RH_BRIDGE»
import «research.GLOBAL_RETURNED_CORE_STOKES_NATURAL_PERIOD_WHEEL»
import «research.STOKES_ENDPOINT_MAX_ALIGNMENT_FRAME»
import «research.STABLE_FAR_PERRON_QUARTER_FRAME_BOUND»

/-!
# Physical Stokes boundary -> natural prime-period frame interface

This file fixes the exact natural frame carrier and eliminates every auxiliary
frame side condition in the RH-consumer regime.

Let
  S_R = primesUpTo (sqrt X_R) \ {2}
on the natural square-sensitive Stokes torus, with endpoint length X_R.
Then:
* every p in S_R is prime;
* p divides the natural torus modulus (indeed p^2 does);
* reciprocal-square mass is at most 1/4;
* X_R <= R^2;
* |S_R| <= R.

Hence the compiled frame majorant is at most (5/4) R^2.

The only remaining analytic/arithmetic step is intentionally explicit:
dominate the exact signed final Stokes boundary by a fixed multiple of this
physical prime-period frame. No such domination is manufactured here by
triangle inequality or by dropping mixed corrected-conductor channels.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-! ## Elementary squarefree two-prime support -/

/-- **Centered two-prime comb support is exactly the `p*q` lattice.**

On a squarefree physical site, each local square-sensitive prime comb is
Boolean: `+1` off the prime and `-1` on the prime.  Centering at `1` therefore
kills every site except those carrying both distinct prime coordinates.
Coprimality identifies those common sites exactly with multiples of `p*q`.

This is the literal arithmetic form of the statement that, for example, the
`3` and `11` coordinates meet only at `33, 66, 99, ...`. -/
theorem centered_localPrimeComb_product_eq_four_twoPrimeIndicator
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hsq : Squarefree n) :
    (localPrimeComb p n - 1) * (localPrimeComb q n - 1) =
      if p * q ∣ n then (4 : ℤ) else 0 := by
  rw [localPrimeComb_eq_ite_dvd_of_squarefree hp hsq,
    localPrimeComb_eq_ite_dvd_of_squarefree hq hsq]
  have hcop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpdq
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpdq)
  by_cases hpn : p ∣ n
  · by_cases hqn : q ∣ n
    · have hpqdvd : p * q ∣ n :=
        hcop.mul_dvd_of_dvd_of_dvd hpn hqn
      simp [hpn, hqn, hpqdvd]
    · have hpqNot : ¬ p * q ∣ n := by
        intro hpqdvd
        apply hqn
        exact dvd_trans ⟨p, by ring⟩ hpqdvd
      simp [hpn, hqn, hpqNot]
  · have hpqNot : ¬ p * q ∣ n := by
      intro hpqdvd
      apply hpn
      exact dvd_trans ⟨q, rfl⟩ hpqdvd
    simp [hpn, hpqNot]

/-- The centered two-prime interaction is nonzero exactly at a physical
`p*q` multiple. -/
theorem centered_localPrimeComb_product_ne_zero_iff_twoPrime_dvd
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hsq : Squarefree n) :
    (localPrimeComb p n - 1) * (localPrimeComb q n - 1) ≠ 0 ↔
      p * q ∣ n := by
  rw [centered_localPrimeComb_product_eq_four_twoPrimeIndicator hp hq hpq hsq]
  by_cases hdiv : p * q ∣ n <;> simp [hdiv]


/-- Actual odd prime-period coordinates of the natural Stokes wheel. -/
def lowOwnerStokesOddPrimePeriodSet (R : ℕ) : Finset ℕ :=
  (lowOwnerStokesWheelPrimes R).erase 2

theorem lowOwnerStokesOddPrimePeriodSet_prime
    {R p : ℕ} (hp : p ∈ lowOwnerStokesOddPrimePeriodSet R) :
    p.Prime := by
  exact lowOwnerStokesWheelPrimes_prime (Finset.mem_erase.mp hp).2

theorem lowOwnerStokesOddPrimePeriodSet_dvd_naturalModulus
    {R p : ℕ} (hR : 56 ≤ R)
    (hp : p ∈ lowOwnerStokesOddPrimePeriodSet R) :
    p ∣ (lowOwnerStokesNaturalWheelSystem R hR).modulus := by
  have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
    (Finset.mem_erase.mp hp).2
  exact dvd_trans (dvd_pow_self p (by norm_num))
    (prime_sq_dvd_lowOwnerStokesNaturalWheelModulus hR hpWheel)

theorem lowOwnerStokesOddPrimePeriodSet_reciprocalSquareBudget_le_quarter
    (R : ℕ) :
    (∑ p ∈ lowOwnerStokesOddPrimePeriodSet R,
      ((1 : ℝ) / (p : ℝ)) ^ 2) ≤ 1 / 4 := by
  unfold lowOwnerStokesOddPrimePeriodSet lowOwnerStokesWheelPrimes
  simpa [div_pow] using
    (oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter
      (Nat.sqrt (squareRootEndpoint R)))

theorem lowOwnerStokesOddPrimePeriodSet_card_le_root
    {R : ℕ} (hR : 1 ≤ R) :
    (lowOwnerStokesOddPrimePeriodSet R).card ≤ R := by
  have hroot : Nat.sqrt (squareRootEndpoint R) < R := by
    apply (Nat.sqrt_lt').2
    unfold squareRootEndpoint
    have hpos : 0 < R ^ 2 := by positivity
    omega
  have hsub :
      lowOwnerStokesOddPrimePeriodSet R ⊆ Finset.range R := by
    intro p hp
    have hpWheel : p ∈ lowOwnerStokesWheelPrimes R :=
      (Finset.mem_erase.mp hp).2
    have hpCut : p ≤ Nat.sqrt (squareRootEndpoint R) := by
      unfold lowOwnerStokesWheelPrimes at hpWheel
      exact (mem_primesUpTo.mp hpWheel).2
    exact Finset.mem_range.mpr (hpCut.trans_lt hroot)
  simpa using Finset.card_le_card hsub

/-- The compiled reciprocal prime-period frame on the literal physical odd
Stokes coordinates and the natural square-sensitive torus. -/
def lowOwnerStokesOddPrimePeriodFrameMajorant
    (R : ℕ) (hR : 56 ≤ R) : ℝ :=
  primePeriodReciprocalFrameMajorant
    (lowOwnerStokesNaturalWheelSystem R hR)
    (squareRootEndpoint R)
    (lowOwnerStokesOddPrimePeriodSet R)

/-- All side conditions of the existing maximum-alignment theorem hold on the
actual Stokes wheel. -/
theorem lowOwnerStokesOddPrimePeriodFrameMajorant_le_five_fourths_root_sq
    {R : ℕ} (hR : 56 ≤ R) :
    lowOwnerStokesOddPrimePeriodFrameMajorant R hR ≤
      (5 / 4 : ℝ) * (R : ℝ) ^ 2 := by
  unfold lowOwnerStokesOddPrimePeriodFrameMajorant
  apply primePeriodReciprocalFrameMajorant_le_five_fourths_root_sq
  · intro p hp
    exact lowOwnerStokesOddPrimePeriodSet_prime hp
  · intro p hp
    exact lowOwnerStokesOddPrimePeriodSet_dvd_naturalModulus hR hp
  · exact lowOwnerStokesOddPrimePeriodSet_reciprocalSquareBudget_le_quarter R
  · unfold squareRootEndpoint
    exact Nat.sub_le _ _
  · exact lowOwnerStokesOddPrimePeriodSet_card_le_root (by omega)

/-- Every admissible lower critical envelope is at least one.  This lets a
root-scale frame estimate feed the existing R^2*K terminal interface without
changing the arithmetic constant. -/
theorem lowerMertensCriticalEnvelope_one_le
    {R : ℕ} {K : ℝ} (hR : 1 ≤ R)
    (hK : LowerMertensCriticalEnvelope R K) :
    1 ≤ K := by
  have h0 := hK.2 0 (by omega)
  norm_num [mertensSummatoryInt] at h0
  exact h0

/-- Exact remaining physical bridge.  The source is the already-identified
final signed Stokes boundary; the target is the actual natural odd-prime frame.
No surrogate boundary or hidden frame hypothesis occurs in the statement. -/
def LowOwnerStokesPrimePeriodFrameDomination (C : ℝ) : Prop :=
  ∀ (R : ℕ) (hR : 56 ≤ R),
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

/-- Any fixed physical domination constant now yields the exact final Stokes
boundary bound consumed by the RH chain. -/
theorem finalStokesBoundaryBound_of_primePeriodFrameDomination
    {C : ℝ} (hC : 0 ≤ C)
    (hBridge : LowOwnerStokesPrimePeriodFrameDomination C) :
    LowOwnerFinalStokesBoundaryBound ((5 / 4 : ℝ) * C) := by
  intro R K hR hK
  have hphysical := hBridge R hR
  have hframe :=
    lowOwnerStokesOddPrimePeriodFrameMajorant_le_five_fourths_root_sq hR
  have hscaled :
      C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR ≤
        C * ((5 / 4 : ℝ) * (R : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hframe hC
  have hKone : 1 ≤ K :=
    lowerMertensCriticalEnvelope_one_le (by omega) hK
  have hcoef :
      0 ≤ ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 := by
    positivity
  have hKmul :=
    mul_le_mul_of_nonneg_left hKone hcoef
  calc
    lowOwnerCanonicalSignedStokesFinalBoundary R ≤
        C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR := hphysical
    _ ≤ C * ((5 / 4 : ℝ) * (R : ℝ) ^ 2) := hscaled
    _ = ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 := by ring
    _ ≤ ((5 / 4 : ℝ) * C) * (R : ℝ) ^ 2 * K := by
      simpa [mul_assoc] using hKmul

/-- Once the exact physical payload-to-frame domination is supplied, no further
Stokes, frame, envelope, or terminal plumbing remains before RH. -/
theorem riemannHypothesis_of_primePeriodFrameDomination
    {C : ℝ} (hC : 0 ≤ C)
    (hBridge : LowOwnerStokesPrimePeriodFrameDomination C) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_finalStokesBoundaryBound
    (by positivity)
    (finalStokesBoundaryBound_of_primePeriodFrameDomination hC hBridge)

/-- Unit-constant version of the remaining physical bridge. -/
def LowOwnerStokesPrimePeriodFrameBridge : Prop :=
  LowOwnerStokesPrimePeriodFrameDomination 1

theorem riemannHypothesis_of_primePeriodFrameBridge
    (hBridge : LowOwnerStokesPrimePeriodFrameBridge) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_primePeriodFrameDomination
    (C := (1 : ℝ)) (by norm_num) hBridge

end RHLean.Proof
