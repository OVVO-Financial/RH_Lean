import Mathlib

/-!
# Positive residue-count energy from the integral Vandermonde

The pair multiplicities of the consecutive native integer slots give a
positive correction to the complete von Mangoldt ramp, rather than a
second signed approximation to it. No RH-scale lower estimate of this
energy is assumed or asserted.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace RHLean.Analysis.NativeVandermondeResidue

/-- Unordered pairs of consecutive integer slots whose differences are
positive multiples of d, with their literal multiplicities. -/
def collision (n d : ℕ) : ℝ :=
  ∑ k ∈ (Icc 1 n).filter (fun k => d ∣ k), ((n:ℝ)-k)

/-- Balanced residue counts have remainder r slots above the quotient
and d-r slots at the quotient. Their squared deviation from n/d is
r(d-r)/d. -/
def residueEnergy (n d : ℕ) : ℝ :=
  (n%d:ℕ) * ((d:ℝ)-(n%d:ℕ))/(d:ℝ)

theorem residueEnergy_nonneg (n d : ℕ) (hd : 0 < d) :
    0 ≤ residueEnergy n d := by
  unfold residueEnergy
  have h : ((n%d:ℕ):ℝ) ≤ (d:ℝ) := by
    exact_mod_cast (Nat.mod_lt n hd).le
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h))
    (Nat.cast_nonneg _)

private theorem progression_sum (a b : ℝ) (q : ℕ) :
    (∑ j ∈ range q, (a-b*((j:ℝ)+1))) =
      (q:ℝ)*a-b*(q:ℝ)*((q:ℝ)+1)/2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- Exact enumeration by the positive multiples d,2d,...,floor(n/d)d. -/
theorem collision_formula (n d : ℕ) (hd : 0 < d) :
    collision n d =
      (n/d:ℕ)*(n:ℝ)-(d:ℝ)*(n/d:ℕ)*((n/d:ℕ)+1:ℝ)/2 := by
  have h : collision n d = ∑ j ∈ range (n/d), ((n:ℝ)-(d:ℝ)*((j:ℝ)+1)) := by
    unfold collision
    symm
    refine Finset.sum_bij (fun j _ => d*(j+1)) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := (Nat.le_div_iff_mul_le hd).mp (Nat.succ_le_of_lt (mem_range.mp hj))
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by positivity, by simpa only [Nat.mul_comm] using hj'⟩,
        ⟨j+1,rfl⟩⟩
    · intro i _ j _ hij
      have h' := Nat.eq_of_mul_eq_mul_left hd hij
      omega
    · intro k hk
      obtain ⟨hk,hdvd⟩ := mem_filter.mp hk
      obtain ⟨u,rfl⟩ := hdvd
      have hu : 0 < u := by
        by_contra! h
        have hz : u = 0 := by omega
        simp [hz] at hk
      have hq : u ≤ n/d := (Nat.le_div_iff_mul_le hd).mpr
        (by simpa only [Nat.mul_comm] using (mem_Icc.mp hk).2)
      refine ⟨u-1,mem_range.mpr (by omega),?_⟩
      rw [Nat.sub_add_cancel (by omega : 1 ≤ u)]
    · intro j _
      push_cast
      ring
  rw [h, progression_sum]

/-- The true-zero correction in the pair count, with its exact sign.
The equality is not an asymptotic prime-distribution statement. -/
theorem collision_residue (n d : ℕ) (hd : 0 < d) :
    2*collision n d = (n:ℝ)*((n:ℝ)/(d:ℝ)-1)+residueEnergy n d := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hh := congrArg (fun k : ℕ => (k:ℝ)) (Nat.mod_add_div n d)
  push_cast at hh
  have hn : (n:ℝ) = (d:ℝ)*(n/d:ℕ)+(n%d:ℕ) := by linarith only [hh]
  rw [collision_formula n d hd, residueEnergy, hn]
  field_simp [hdR]
  <;> ring

/-- Literal logarithm of the consecutive-slot Vandermonde product. -/
def pairLog (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, ((n:ℝ)-k)*Real.log (k:ℝ)

/-- Complete native ramp, with all proper prime powers retained. -/
def ramp (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, Λ d*((n:ℝ)/(d:ℝ)-1)

def weightedEnergy (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, Λ d*residueEnergy n d

theorem weightedEnergy_nonneg (n : ℕ) : 0 ≤ weightedEnergy n := by
  exact sum_nonneg fun d hd =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (residueEnergy_nonneg n d (by have := (mem_Icc.mp hd).1; omega))

/-- Interchange the actual difference/prime-power sums. This is the
divisor identity for log k, not a prime-number approximation. -/
theorem pairLog_collision (n : ℕ) :
    (∑ d ∈ Icc 1 n, Λ d * collision n d) = pairLog n := by
  classical
  have hdiv (k : ℕ) (hk : k ∈ Icc 1 n) :
      ((Icc 1 n).filter (fun d => d ∣ k)) = k.divisors := by
    have hk' := mem_Icc.mp hk
    have hk0 : k ≠ 0 := by omega
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨h.2,hk0⟩
    · intro h
      have hd0 : d ≠ 0 := by
        intro hz
        subst d
        exact hk0 (zero_dvd_iff.mp h.1)
      exact ⟨⟨Nat.pos_of_ne_zero hd0,(Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h.1).trans hk'.2⟩,h.1⟩
  unfold collision pairLog
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro k hk
  calc
    _ = ∑ d ∈ Icc 1 n, (if d ∣ k then Λ d else 0)*((n:ℝ)-k) := by
      apply sum_congr rfl
      intro d _
      split_ifs <;> ring
    _ = _ := by
      rw [← sum_mul, ← Finset.sum_filter, hdiv k hk, ArithmeticFunction.vonMangoldt_sum]
      ring

/-- Exact positive residue-energy reformulation of the signed ramp. -/
theorem pairLog_energy (n : ℕ) :
    2*pairLog n = (n:ℝ)*ramp n + weightedEnergy n := by
  rw [← pairLog_collision, Finset.mul_sum]
  unfold ramp weightedEnergy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have h := collision_residue n d (by have := (mem_Icc.mp hd).1; omega)
  calc
    2*(Λ d*collision n d) = Λ d*(2*collision n d) := by ring
    _ = _ := by rw [h]; ring

theorem ramp_le_pairLog (n : ℕ) (hn : 0 < n) :
    ramp n ≤ 2*pairLog n/(n:ℝ) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hp).2
  linarith only [pairLog_energy n, weightedEnergy_nonneg n]

end RHLean.Analysis.NativeVandermondeResidue
