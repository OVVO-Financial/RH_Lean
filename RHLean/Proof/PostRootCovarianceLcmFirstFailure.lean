import Mathlib
import RHLean.Proof.PostRootCovarianceLcmBoundaryClosure

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- Real indicator for the literal super-endpoint lcm wall. -/
def superLcmIndicator (W m n : ℕ) : ℝ :=
  if W < Nat.lcm m n then 1 else 0

private theorem firstFailure_lcm_prime_mul_left
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm (p * a) b = p * Nat.lcm a b := by
  apply Nat.dvd_antisymm
  · apply (Nat.lcm_dvd_iff).2
    constructor
    · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left a b)
    · rcases Nat.dvd_lcm_right a b with ⟨k, hk⟩
      refine ⟨p * k, ?_⟩
      omega
  · have hpTarget : p ∣ Nat.lcm (p * a) b :=
      (show p ∣ p * a from ⟨a, rfl⟩).trans (Nat.dvd_lcm_left (p * a) b)
    have haTarget : a ∣ Nat.lcm (p * a) b :=
      (show a ∣ p * a from ⟨p, by simp [Nat.mul_comm]⟩).trans
        (Nat.dvd_lcm_left (p * a) b)
    have hbTarget : b ∣ Nat.lcm (p * a) b := Nat.dvd_lcm_right (p * a) b
    have hlcmTarget : Nat.lcm a b ∣ Nat.lcm (p * a) b :=
      (Nat.lcm_dvd_iff).2 ⟨haTarget, hbTarget⟩
    have hlcmMul : Nat.lcm a b ∣ a * b := by
      apply (Nat.lcm_dvd_iff).2
      exact ⟨⟨b, rfl⟩, ⟨a, by simp [Nat.mul_comm]⟩⟩
    have hpNotLcm : ¬ p ∣ Nat.lcm a b := by
      intro hpLcm
      have hpMul : p ∣ a * b := hpLcm.trans hlcmMul
      rcases hp.dvd_mul.mp hpMul with hpA | hpB
      · exact hpa hpA
      · exact hpb hpB
    have hcop : Nat.Coprime p (Nat.lcm a b) :=
      hp.coprime_iff_not_dvd.mpr hpNotLcm
    exact hcop.mul_dvd_of_dvd_of_dvd hpTarget hlcmTarget

private theorem firstFailure_lcm_prime_mul_right
    {p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    Nat.lcm a (p * b) = p * Nat.lcm a b := by
  rw [Nat.lcm_comm]
  simpa [Nat.lcm_comm] using
    firstFailure_lcm_prime_mul_left hp hpb hpa

/-- **Exact one-prime LCM wall stencil.**

For a prime fresh to both parent coordinates, the three non-base corners have
one common lcm `p*lcm(a,b)`.  Hence the complete four-corner indicator
finite-difference vanishes except at the literal first crossing

`lcm(a,b) <= W < p*lcm(a,b)`, 

where it is exactly `-1`. -/
theorem superLcmIndicator_fourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    superLcmIndicator W a b -
        superLcmIndicator W (p * a) b -
        superLcmIndicator W a (p * b) +
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then -1 else 0 := by
  have hleft := firstFailure_lcm_prime_mul_left hp hpa hpb
  have hright := firstFailure_lcm_prime_mul_right hp hpa hpb
  have hboth : Nat.lcm (p * a) (p * b) = p * Nat.lcm a b := by
    simpa only [Nat.lcm_mul_left]
  unfold superLcmIndicator
  rw [hleft, hright, hboth]
  have hle : Nat.lcm a b ≤ p * Nat.lcm a b := by
    calc
      Nat.lcm a b = 1 * Nat.lcm a b := by simp
      _ ≤ p * Nat.lcm a b := Nat.mul_le_mul_right _ hp.one_le
  by_cases hbase : W < Nat.lcm a b
  · have hupper : W < p * Nat.lcm a b := hbase.trans_le hle
    simp [hbase, hupper]
  · have hbaseLe : Nat.lcm a b ≤ W := Nat.le_of_not_gt hbase
    by_cases hupper : W < p * Nat.lcm a b
    · simp [hbase, hbaseLe, hupper]
    · simp [hbase, hupper]

/-- **Möbius-weighted form of the same wall stencil.**  The fresh-prime sign
reversal turns the four physical pair corners into the Boolean finite
difference above.  Thus the entire signed Euler square is zero off the first
LCM wall and equals minus the old pair weight on the wall. -/
theorem realMoebiusSuperLcmFourCorner_eq_firstFailure
    {W p a b : ℕ} (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) :
    (realMoebiusStep a * realMoebiusStep b) * superLcmIndicator W a b +
      (realMoebiusStep (p * a) * realMoebiusStep b) *
        superLcmIndicator W (p * a) b +
      (realMoebiusStep a * realMoebiusStep (p * b)) *
        superLcmIndicator W a (p * b) +
      (realMoebiusStep (p * a) * realMoebiusStep (p * b)) *
        superLcmIndicator W (p * a) (p * b) =
      if Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b then
        -(realMoebiusStep a * realMoebiusStep b)
      else 0 := by
  rw [realMoebiusStep_mul_prime_eq_neg hp hpa,
    realMoebiusStep_mul_prime_eq_neg hp hpb]
  have hwall := superLcmIndicator_fourCorner_eq_firstFailure
    (W := W) hp hpa hpb
  by_cases hcross : Nat.lcm a b ≤ W ∧ W < p * Nat.lcm a b
  · rw [if_pos hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall
  · rw [if_neg hcross] at hwall ⊢
    linear_combination (realMoebiusStep a * realMoebiusStep b) * hwall

end RHLean.Proof
