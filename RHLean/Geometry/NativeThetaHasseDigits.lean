import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Hasse coefficients of a residue and its coarse exponent

The expansion uses integral binomial polynomials. Terms of excessive coarse
degree are divisible by the full requested prime power.
-/

set_option autoImplicit false
open scoped BigOperators Polynomial
open Polynomial

namespace RHLean.Geometry.NativeTheta.HasseDigits

noncomputable def block (P : ℕ) : ℤ[X] := (1 + X) ^ P - 1

/-- Integral coefficient of the kth coarse binomial polynomial. -/
noncomputable def digitCoeff (P ρ M k : ℕ) : ℤ :=
  (((1 + X) ^ ρ : ℤ[X]) * (block P) ^ k).coeff M

/-- The exact integral Hasse expansion in the binomial basis of the coarse exponent. -/
theorem choose_eq_digit_expansion (P ρ β M : ℕ) :
    ((ρ + P * β).choose M : ℤ) =
      ∑ k ∈ Finset.range (β + 1), digitCoeff P ρ M k * (β.choose k : ℤ) := by
  have hbase : (1 + X : ℤ[X]) ^ P = block P + 1 := (sub_add_cancel _ _).symm
  have he : (1 + X : ℤ[X]) ^ (ρ + P * β) =
      ∑ k ∈ Finset.range (β + 1), (((1 + X) ^ ρ : ℤ[X]) * (block P) ^ k) *
        C (β.choose k : ℤ) := by
    rw [pow_add, pow_mul, hbase, add_pow (block P) 1 β]
    simp only [one_pow, mul_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [C_eq_natCast, mul_assoc]
  rw [← coeff_one_add_X_pow ℤ, he, finsetSum_coeff]
  exact Finset.sum_congr rfl fun k _ => coeff_mul_C _ _ _

private theorem prime_dvd_block_coeff {p : ℕ} (hp : p.Prime) (g j : ℕ) (hj : j < p ^ g) :
    (p : ℤ) ∣ (block (p ^ g)).coeff j := by
  rw [block, coeff_sub, coeff_one_add_X_pow, coeff_one]
  by_cases hz : j = 0
  · subst j
    simp
  · simp only [ite_eq_right hz, sub_zero]
    exact_mod_cast hp.dvd_choose_pow hz hj.ne

/-- Every multiplication by the digit block either spends a full block of
    polynomial degree or provides an extra factor p. -/
theorem prime_pow_dvd_digitCoeff {p : ℕ} (hp : p.Prime) (g ρ M k : ℕ) :
    (p : ℤ) ^ (k - M / (p ^ g)) ∣ digitCoeff (p ^ g) ρ M k := by
  let P := p ^ g
  have hP : 0 < P := pow_pos hp.pos _
  change (p : ℤ) ^ (k - M / P) ∣ (((1 + X) ^ ρ : ℤ[X]) * (block P) ^ k).coeff M
  induction k generalizing M with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, coeff_mul]
    apply Finset.dvd_sum
    rintro ⟨i, j⟩ hij
    have hsum : i + j = M := Finset.mem_antidiagonal.mp hij
    by_cases hj : j < P
    · have hdiv : i / P ≤ M / P := Nat.div_le_div_right (by omega)
      have hpow : k + 1 - M / P ≤ (k - i / P) + 1 := by omega
      refine (pow_dvd_pow (p : ℤ) hpow).trans ?_
      rw [pow_succ]
      exact mul_dvd_mul (ih i) (prime_dvd_block_coeff hp g j hj)
    · have hdiv : i / P + 1 ≤ M / P := by
        rw [← Nat.add_div_right i hP]
        exact Nat.div_le_div_right (by omega)
      exact (pow_dvd_pow (p : ℤ) (by omega : k + 1 - M / P ≤ k - i / P)).trans
        (dvd_mul_of_dvd_left (ih i) _)

/-- Modulo p^c the multi-coordinate expansion is supported on coarse total
    degrees strictly below sum_i floor(M_i / p^g) + c. -/
theorem prime_pow_dvd_prod_digitCoeff_of_degree {ι : Type*} {p : ℕ} (hp : p.Prime)
    (g c : ℕ) (s : Finset ι) (ρ M k : ι → ℕ)
    (h : (∑ i ∈ s, M i / p ^ g) + c ≤ ∑ i ∈ s, k i) :
    (p : ℤ) ^ c ∣ ∏ i ∈ s, digitCoeff (p ^ g) (ρ i) (M i) (k i) := by
  have hs : (∑ i ∈ s, k i) ≤ (∑ i ∈ s, (k i - M i / p ^ g)) +
      (∑ i ∈ s, M i / p ^ g) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    change k i ≤ (k i - M i / p ^ g) + M i / p ^ g
    omega
  have hc : c ≤ ∑ i ∈ s, (k i - M i / p ^ g) := by omega
  refine (pow_dvd_pow (p : ℤ) hc).trans ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => prime_pow_dvd_digitCoeff hp g (ρ i) (M i) (k i)

private theorem choose_cast_eq_sum_range {p : ℕ} (hp : p.Prime) (g c ρ β M B : ℕ)
    (hB : M / p ^ g + c ≤ B) :
    ((ρ + p ^ g * β).choose M : ZMod (p ^ c)) =
      ∑ k ∈ Finset.range B, (digitCoeff (p ^ g) ρ M k : ZMod (p ^ c)) * (β.choose k : ZMod (p ^ c)) := by
  let f (k : ℕ) : ZMod (p ^ c) := (digitCoeff (p ^ g) ρ M k : ZMod (p ^ c)) * β.choose k
  have he : ((ρ + p ^ g * β).choose M : ZMod (p ^ c)) = ∑ k ∈ Finset.range (β + 1), f k := by
    simpa only [f, Int.cast_natCast, Int.cast_sum, Int.cast_mul] using
      congrArg (fun z : ℤ => (z : ZMod (p ^ c))) (choose_eq_digit_expansion (p ^ g) ρ β M)
  change _ = ∑ k ∈ Finset.range B, f k
  rw [he]
  by_cases h : β + 1 ≤ B
  · apply Finset.sum_subset (Finset.range_mono h)
    intro k _ hk
    have hβ : β < k := by
      exact Nat.le_of_not_gt (fun hlt : k < β + 1 => hk (Finset.mem_range.mpr hlt))
    simp only [f, Nat.choose_eq_zero_of_lt hβ, Nat.cast_zero, mul_zero]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : B ≤ β + 1))
    intro k _ hk
    have hk' : B ≤ k := Nat.le_of_not_gt fun hlt => hk (Finset.mem_range.mpr hlt)
    have hc : c ≤ k - M / p ^ g := by omega
    have hd := (pow_dvd_pow (p : ℤ) hc).trans (prime_pow_dvd_digitCoeff hp g ρ M k)
    have hz : (digitCoeff (p ^ g) ρ M k : ZMod (p ^ c)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hd)
    simp only [f, hz, zero_mul]

open scoped Classical in
/-- The bounded support and coefficient array are independent of the coarse
    inputs β. This is a congruence of integer-valued binomial functions. -/
theorem choose_prod_eq_bounded_hasse_sum {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime)
    (g c : ℕ) (ρ M β : ι → ℕ) :
    let B := (∑ i, M i / p ^ g) + c
    (∏ i, ((ρ i + p ^ g * β i).choose (M i) : ZMod (p ^ c))) =
      ∑ k ∈ (Finset.univ : Finset (ι → Fin B)).filter (fun k => (∑ i, (k i).val) < B),
        ∏ i, (digitCoeff (p ^ g) (ρ i) (M i) (k i).val : ZMod (p ^ c)) *
          ((β i).choose (k i).val : ZMod (p ^ c)) := by
  let B := (∑ i, M i / p ^ g) + c
  let f (i : ι) (k : Fin B) : ZMod (p ^ c) :=
    (digitCoeff (p ^ g) (ρ i) (M i) k.val : ZMod (p ^ c)) * (β i).choose k.val
  let F (k : ι → Fin B) := ∏ i, f i (k i)
  change (∏ i, ((ρ i + p ^ g * β i).choose (M i) : ZMod (p ^ c))) =
    ∑ k ∈ (Finset.univ : Finset (ι → Fin B)).filter (fun k => (∑ i, (k i).val) < B), F k
  have hfull : (∏ i, ((ρ i + p ^ g * β i).choose (M i) : ZMod (p ^ c))) = ∑ k, F k := by
    calc
      _ = ∏ i, ∑ k : Fin B, f i k := by
        apply Finset.prod_congr rfl
        intro i _
        have hM : M i / p ^ g ≤ ∑ j, M j / p ^ g :=
          Finset.single_le_sum (f := fun j => M j / p ^ g)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        dsimp only [f]
        rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
          (digitCoeff (p ^ g) (ρ i) (M i) k : ZMod (p ^ c)) * (β i).choose k) B]
        exact choose_cast_eq_sum_range hp g c (ρ i) (β i) (M i) B (Nat.add_le_add_right hM c)
      _ = _ := Fintype.prod_sum f
  rw [hfull]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _ hk
  have hhi : B ≤ ∑ i, (k i).val := Nat.le_of_not_gt fun hlt =>
    hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)
  have hd := prime_pow_dvd_prod_digitCoeff_of_degree hp g c Finset.univ ρ M (fun i => (k i).val) hhi
  have hz : ((∏ i, digitCoeff (p ^ g) (ρ i) (M i) (k i).val : ℤ) : ZMod (p ^ c)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hd)
  dsimp only [F, f]
  rw [Finset.prod_mul_distrib, ← Int.cast_prod, hz, zero_mul]

end RHLean.Geometry.NativeTheta.HasseDigits
