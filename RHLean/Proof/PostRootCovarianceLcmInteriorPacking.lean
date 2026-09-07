import Mathlib
import RHLean.Proof.PostRootCovarianceLcmBoundary

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The part of one removed post-root prime family whose pair lcm still fits
below the physical endpoint. -/
def postRootPrimePhysicalInteriorLcmCarrier
    (W p : ℕ) : Finset (ℕ × ℕ) :=
  (postRootPrimePhysicalPairCarrier W p).filter fun mn =>
    Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_postRootPrimePhysicalInteriorLcmCarrier
    {W p : ℕ} {mn : ℕ × ℕ} :
    mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p ↔
      mn ∈ postRootPrimePhysicalPairCarrier W p ∧
        Nat.lcm mn.1 mn.2 ≤ W := by
  simp [postRootPrimePhysicalInteriorLcmCarrier]

/-- **Exact quotient scaling of a post-root lcm interior.**  Multiplication by
`p` is a weight-preserving bijection from the complete positive lcm interior at
scale `W / p` onto the physical lcm interior of the removed `p`-family.

The two Möbius sign reversals cancel, while `lcm (p*a) (p*b) =
p*lcm(a,b)` transports the multiplicative cutoff exactly. -/
theorem sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ ab ∈ moebiusLcmInteriorPositiveCarrier (W / p),
        realMoebiusStep ab.1 * realMoebiusStep ab.2 := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
  have hquotlt : W / p < p :=
    (Nat.div_lt_iff_lt_mul hpPrime.pos).2 hWpp
  symm
  refine Finset.sum_bij
    (fun ab _hab => (p * ab.1, p * ab.2)) ?_ ?_ ?_ ?_
  · intro ab hab
    rcases mem_moebiusLcmInteriorPositiveCarrier.mp hab with
      ⟨ha, hb, hablt, hlcm⟩
    rcases Finset.mem_Icc.mp ha with ⟨ha1, haQ⟩
    rcases Finset.mem_Icc.mp hb with ⟨hb1, hbQ⟩
    have haW : p * ab.1 ≤ W := by
      have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 haQ
      simpa [Nat.mul_comm] using h
    have hbW : p * ab.2 ≤ W := by
      have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 hbQ
      simpa [Nat.mul_comm] using h
    have habp : p * ab.1 < p * ab.2 :=
      (Nat.mul_lt_mul_left hpPrime.pos).2 hablt
    have hlcmW : Nat.lcm (p * ab.1) (p * ab.2) ≤ W := by
      have hmul : p * Nat.lcm ab.1 ab.2 ≤ W := by
        have h := (Nat.le_div_iff_mul_le hpPrime.pos).1 hlcm
        simpa [Nat.mul_comm] using h
      simpa [lcm_mul_left] using hmul
    apply mem_postRootPrimePhysicalInteriorLcmCarrier.mpr
    constructor
    · apply mem_postRootPrimePhysicalPairCarrier.mpr
      exact ⟨Nat.mul_pos hpPrime.pos (by omega), haW,
        Nat.mul_pos hpPrime.pos (by omega), hbW, habp,
        ⟨ab.1, by simp [Nat.mul_comm]⟩,
        ⟨ab.2, by simp [Nat.mul_comm]⟩⟩
    · exact hlcmW
  · intro a ha b hb hab
    apply Prod.ext
    · exact Nat.eq_of_mul_eq_mul_left hpPrime.pos (congrArg Prod.fst hab)
    · exact Nat.eq_of_mul_eq_mul_left hpPrime.pos (congrArg Prod.snd hab)
  · intro mn hmn
    rcases mem_postRootPrimePhysicalInteriorLcmCarrier.mp hmn with
      ⟨hfamily, hlcmW⟩
    rcases mem_postRootPrimePhysicalPairCarrier.mp hfamily with
      ⟨hm1, hmW, hn1, hnW, hmnlt, hpm, hpn⟩
    let a := mn.1 / p
    let b := mn.2 / p
    have hma : p * a = mn.1 := Nat.mul_div_cancel' hpm
    have hnb : p * b = mn.2 := Nat.mul_div_cancel' hpn
    have ha1 : 1 ≤ a := by
      by_contra h
      have ha0 : a = 0 := by omega
      rw [ha0, mul_zero] at hma
      omega
    have hb1 : 1 ≤ b := by
      by_contra h
      have hb0 : b = 0 := by omega
      rw [hb0, mul_zero] at hnb
      omega
    have haQ : a ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [Nat.mul_comm, hma] using hmW
    have hbQ : b ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      simpa [Nat.mul_comm, hnb] using hnW
    have hablt : a < b := by
      apply (Nat.mul_lt_mul_left hpPrime.pos).1
      simpa [hma, hnb] using hmnlt
    have hlcmQ : Nat.lcm a b ≤ W / p := by
      apply (Nat.le_div_iff_mul_le hpPrime.pos).2
      have hlcmScaled : Nat.lcm (p * a) (p * b) ≤ W := by
        simpa [hma, hnb] using hlcmW
      simpa [lcm_mul_left, Nat.mul_comm] using hlcmScaled
    refine ⟨(a, b), ?_, ?_⟩
    · exact mem_moebiusLcmInteriorPositiveCarrier.mpr ⟨
        Finset.mem_Icc.mpr ⟨ha1, haQ⟩,
        Finset.mem_Icc.mpr ⟨hb1, hbQ⟩,
        hablt, hlcmQ⟩
    · ext <;> simp [a, b, hma, hnb]
  · intro ab hab
    rcases mem_moebiusLcmInteriorPositiveCarrier.mp hab with
      ⟨ha, hb, _hablt, _hlcm⟩
    have haP : ab.1 < p :=
      (Finset.mem_Icc.mp ha).2.trans_lt hquotlt
    have hbP : ab.2 < p :=
      (Finset.mem_Icc.mp hb).2.trans_lt hquotlt
    exact (realMoebiusStep_prime_mul_pair hpPrime haP hbP).symm

/-- Every removed post-root family has nonpositive complete-lcm interior mass. -/
theorem sum_postRootPrimePhysicalInteriorLcmCarrier_nonpos
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    (∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ 0 := by
  rw [sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp]
  exact sum_realMoebiusStep_lcmInteriorPositive_nonpos (W / p)

/-- Its negative size is at most its quotient seat count `W / p`. -/
theorem neg_quotient_le_sum_postRootPrimePhysicalInteriorLcmCarrier
    {W p : ℕ} (hp : p ∈ postRootPrimeFamilySet W) :
    -((W / p : ℕ) : ℝ) ≤
      ∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  rw [sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp]
  exact neg_endpoint_le_sum_realMoebiusStep_lcmInteriorPositive (W / p)

end RHLean.Proof
