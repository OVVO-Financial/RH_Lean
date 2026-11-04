import Mathlib
import RHLean.Analysis.NativePNTMertens

/-!
Finite arithmetic core of Coordinator C29, accepted with scope in
20261103-referee-5. The residue carrier is the original Nyman carrier.
The final theorem does not assume an error bound or an RH-strength premise.
The finite weighted comparison retains both overlapping dyadic index sets.
No bound on the full approximation error or analytic RH consequence is asserted.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanResidue (k m : Nat) : Real := (m % k : Nat) / (k : Real)

def nymanResidual (N : Nat) (c : Nat -> Real) (m : Nat) : Real :=
  1 - Finset.sum (Icc 2 N) (fun k => c k * nymanResidue k m)

def nymanLogKernel (N k : Nat) : Real :=
  (ArithmeticFunction.moebius k : Real) *
    (Real.log (N : Real) - Real.log (k : Real))

def nymanLogCoefficient (N k : Nat) : Real :=
  -nymanLogKernel N k / Real.log (N : Real)

def nymanPsi (m : Nat) : Real :=
  Finset.sum (Icc 1 m) (fun n => ArithmeticFunction.vonMangoldt n)

def nymanCarry (k m : Nat) : Real :=
  ((2 * m / k : Nat) : Real) - 2 * ((m / k : Nat) : Real)

theorem nymanLogCoefficient_eq_original
    (N k : Nat) (hN : 2 <= N) (hk : 1 <= k) :
    nymanLogCoefficient N k =
      -(ArithmeticFunction.moebius k : Real) *
        Real.log ((N : Real) / (k : Real)) / Real.log (N : Real) := by
  have hNz : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hkz : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [Real.log_div hNz hkz]
  unfold nymanLogCoefficient nymanLogKernel
  ring

theorem nymanResidue_eq_div_sub_floor (k m : Nat) (hk : 1 <= k) :
    nymanResidue k m =
      (m : Real) / (k : Real) - ((m / k : Nat) : Real) := by
  have hkz : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hmod : ((m % k : Nat) : Real) +
      (k : Real) * ((m / k : Nat) : Real) = (m : Real) := by
    exact_mod_cast Nat.mod_add_div m k
  unfold nymanResidue
  field_simp [hkz]
  nlinarith only [hmod]

theorem nymanResidue_dyadic (k m : Nat) (hk : 1 <= k) :
    nymanResidue k (2 * m) - 2 * nymanResidue k m =
      -nymanCarry k m := by
  rw [nymanResidue_eq_div_sub_floor k (2 * m) hk,
    nymanResidue_eq_div_sub_floor k m hk]
  unfold nymanCarry
  push_cast
  ring

theorem nymanCarry_eq_zero_of_lt (k m : Nat) (h : 2 * m < k) :
    nymanCarry k m = 0 := by
  have hm : m < k := by omega
  simp [nymanCarry, Nat.div_eq_of_lt h, Nat.div_eq_of_lt hm]

theorem nymanResidual_dyadic_eq_carry (N m : Nat) (c : Nat -> Real) :
    nymanResidual N c (2 * m) - 2 * nymanResidual N c m =
      -1 + Finset.sum (Icc 2 N) (fun k => c k * nymanCarry k m) := by
  have hsum :
      Finset.sum (Icc 2 N) (fun k => c k * nymanCarry k m) =
        2 * Finset.sum (Icc 2 N) (fun k => c k * nymanResidue k m) -
          Finset.sum (Icc 2 N) (fun k => c k * nymanResidue k (2 * m)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hd := nymanResidue_dyadic k m (by
      have := (Finset.mem_Icc.mp hk).1
      omega)
    nlinarith only [congrArg (fun z : Real => c k * z) hd]
  unfold nymanResidual
  rw [hsum]
  ring

theorem nymanResidual_dyadic_congr_low
    (N H m : Nat) (c b : Nat -> Real) (hm : 2 * m <= H)
    (hlow : ∀ k, k ∈ Icc 2 N -> k <= H -> c k = b k) :
    nymanResidual N c (2 * m) - 2 * nymanResidual N c m =
      nymanResidual N b (2 * m) - 2 * nymanResidual N b m := by
  rw [nymanResidual_dyadic_eq_carry, nymanResidual_dyadic_eq_carry]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkH : k <= H
  · rw [hlow k hk hkH]
  · rw [nymanCarry_eq_zero_of_lt k m (by omega)]
    simp

theorem nyman_sum_mul_floor_eq_divisor_sum (A : Nat) (f : Nat -> Real) :
    Finset.sum (Icc 1 A) (fun d => f d * ((A / d : Nat) : Real)) =
      Finset.sum (Icc 1 A) (fun n => Finset.sum n.divisors f) := by
  classical
  have key : ∀ d : Nat,
      f d * ((A / d : Nat) : Real) =
        Finset.sum (Icc 1 A) (fun n => if d ∣ n then f d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, nativeCardMultiplesIcc]
    ring
  calc
    _ = Finset.sum (Icc 1 A) (fun d =>
        Finset.sum (Icc 1 A) (fun n => if d ∣ n then f d else 0)) :=
      Finset.sum_congr rfl (fun d _ => key d)
    _ = Finset.sum (Icc 1 A) (fun n =>
        Finset.sum (Icc 1 A) (fun d => if d ∣ n then f d else 0)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [<- Finset.sum_filter]
      apply Finset.sum_congr
      · ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨hd, hdiv⟩
          exact ⟨hdiv, by have := Finset.mem_Icc.mp hn; omega⟩
        · rintro ⟨hdiv, hn0⟩
          have hnpos : 0 < n := by have := Finset.mem_Icc.mp hn; omega
          have hdpos := Nat.pos_of_dvd_of_pos hdiv hnpos
          have hdle := Nat.le_of_dvd hnpos hdiv
          exact ⟨⟨hdpos, by have := Finset.mem_Icc.mp hn; omega⟩, hdiv⟩
      · intro d hd
        rfl

theorem nymanLogKernel_divisor_sum (N n : Nat) (hn : 1 <= n) :
    Finset.sum n.divisors (nymanLogKernel N) =
      Real.log (N : Real) * (if n = 1 then 1 else 0) +
        ArithmeticFunction.vonMangoldt n := by
  have hmu : Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : Real)) =
      if n = 1 then 1 else 0 := by
    exact_mod_cast nativeSumMoebiusDivisors n hn
  have hlog := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  change Finset.sum n.divisors (fun d =>
    (ArithmeticFunction.moebius d : Real) * Real.log (d : Real)) =
      -ArithmeticFunction.vonMangoldt n at hlog
  simp only [nymanLogKernel, mul_sub, Finset.sum_sub_distrib]
  rw [<- Finset.sum_mul, hmu, hlog]
  ring

theorem nymanLogKernel_floor_sum (N m : Nat) (hm : 1 <= m) (hmN : m <= N) :
    Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) =
      Real.log (N : Real) + nymanPsi m := by
  have hsub : Icc 1 m ⊆ Icc 1 N := by
    intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hmN⟩
  have hrestrict :
      Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) =
        Finset.sum (Icc 1 m) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkN hkm
    have hmk : m < k := by
      simp only [Finset.mem_Icc] at hkN hkm
      omega
    simp [Nat.div_eq_of_lt hmk]
  rw [hrestrict, nyman_sum_mul_floor_eq_divisor_sum]
  have hsum :
      Finset.sum (Icc 1 m) (fun n => Finset.sum n.divisors (nymanLogKernel N)) =
        Finset.sum (Icc 1 m) (fun n =>
          Real.log (N : Real) * (if n = 1 then 1 else 0) +
            ArithmeticFunction.vonMangoldt n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact nymanLogKernel_divisor_sum N n (Finset.mem_Icc.mp hn).1
  rw [hsum, Finset.sum_add_distrib, <- Finset.mul_sum]
  simp [nymanPsi, Finset.sum_ite_eq', Finset.mem_Icc, hm]

theorem nymanLogKernel_carry_sum (N m : Nat) (hm : 1 <= m)
    (hmN : 2 * m <= N) :
    Finset.sum (Icc 2 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
      -Real.log (N : Real) + nymanPsi (2 * m) - 2 * nymanPsi m := by
  have hsub : Icc 2 N ⊆ Icc 1 N := by
    intro k hk
    have := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hsame :
      Finset.sum (Icc 2 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
        Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * nymanCarry k m) := by
    apply Finset.sum_subset hsub
    intro k hk hnot
    have hk1 : k = 1 := by
      simp only [Finset.mem_Icc] at hk hnot
      omega
    subst k
    simp [nymanCarry]
  rw [hsame]
  have hsplit :
      Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * nymanCarry k m) =
        Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * ((2 * m / k : Nat) : Real)) -
          2 * Finset.sum (Icc 1 N) (fun k => nymanLogKernel N k * ((m / k : Nat) : Real)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    unfold nymanCarry
    ring
  rw [hsplit, nymanLogKernel_floor_sum N (2 * m) (by omega) hmN,
    nymanLogKernel_floor_sum N m hm (by omega)]
  ring

theorem nymanLogCoefficient_dyadic (N m : Nat) (hN : 2 <= N)
    (hm : 1 <= m) (hmN : 2 * m <= N) :
    Real.log (N : Real) *
      (nymanResidual N (nymanLogCoefficient N) (2 * m) -
        2 * nymanResidual N (nymanLogCoefficient N) m) =
      2 * nymanPsi m - nymanPsi (2 * m) := by
  have hL : Real.log (N : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [nymanResidual_dyadic_eq_carry, mul_add, Finset.mul_sum]
  have hterm : ∀ k : Nat,
      Real.log (N : Real) * (nymanLogCoefficient N k * nymanCarry k m) =
        -(nymanLogKernel N k * nymanCarry k m) := by
    intro k
    unfold nymanLogCoefficient
    field_simp [hL] <;> ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib,
    nymanLogKernel_carry_sum N m hm hmN]
  ring

theorem nyman_high_coefficient_annihilator
    (N H m : Nat) (c : Nat -> Real) (hN : 2 <= N) (hHN : H <= N)
    (hm : 1 <= m) (hmH : 2 * m <= H)
    (hlow : ∀ k, k ∈ Icc 2 N -> k <= H ->
      c k = nymanLogCoefficient N k) :
    Real.log (N : Real) *
      (nymanResidual N c (2 * m) - 2 * nymanResidual N c m) =
      2 * nymanPsi m - nymanPsi (2 * m) := by
  rw [nymanResidual_dyadic_congr_low N H m c (nymanLogCoefficient N) hmH hlow]
  exact nymanLogCoefficient_dyadic N m hN hm (hmH.trans hHN)

def nymanWeight (m : Nat) : Real := 1 / ((m : Real) * ((m : Real) + 1))

theorem nymanWeight_nonneg (m : Nat) : 0 <= nymanWeight m := by
  unfold nymanWeight
  positivity

theorem nymanWeight_le_four_doubled (m : Nat) (hm : 1 <= m) :
    nymanWeight m <= 4 * nymanWeight (2 * m) := by
  have hmpos : 0 < (m : Real) := by exact_mod_cast (show 0 < m by omega)
  unfold nymanWeight
  push_cast
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem nyman_dyadic_weighted_bound (X : Nat) (r : Nat -> Real) :
    Finset.sum (Icc 1 X) (fun m => nymanWeight m * (r (2 * m) - 2 * r m) ^ 2) <=
      16 * Finset.sum (Icc 1 (2 * X)) (fun n => nymanWeight n * r n ^ 2) := by
  classical
  let f : Nat -> Real := fun n => nymanWeight n * r n ^ 2
  have hf (n : Nat) : 0 <= f n := mul_nonneg (nymanWeight_nonneg n) (sq_nonneg _)
  have hsmall : Finset.sum (Icc 1 X) f <= Finset.sum (Icc 1 (2 * X)) f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n _ _
      exact hf n
  have himage : (Icc 1 X).image (fun m => 2 * m) ⊆ Icc 1 (2 * X) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  have hdoubled : Finset.sum (Icc 1 X) (fun m => f (2 * m)) <=
      Finset.sum (Icc 1 (2 * X)) f := by
    have he : Finset.sum ((Icc 1 X).image (fun m => 2 * m)) f =
        Finset.sum (Icc 1 X) (fun m => f (2 * m)) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      omega
    rw [← he]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun n _ _ => hf n)
  have hpoint (m : Nat) (hm : m ∈ Icc 1 X) :
      nymanWeight m * (r (2 * m) - 2 * r m) ^ 2 <=
        8 * f (2 * m) + 8 * f m := by
    have hs : (r (2 * m) - 2 * r m) ^ 2 <=
        2 * r (2 * m) ^ 2 + 8 * r m ^ 2 := by
      nlinarith only [sq_nonneg (r (2 * m) + 2 * r m)]
    have hw := mul_le_mul_of_nonneg_right
      (nymanWeight_le_four_doubled m (Finset.mem_Icc.mp hm).1)
      (sq_nonneg (r (2 * m)))
    have hp := mul_le_mul_of_nonneg_left hs (nymanWeight_nonneg m)
    dsimp only [f]
    nlinarith only [hp, hw]
  calc
    _ <= Finset.sum (Icc 1 X) (fun m => 8 * f (2 * m) + 8 * f m) :=
      Finset.sum_le_sum hpoint
    _ = 8 * Finset.sum (Icc 1 X) (fun m => f (2 * m)) + 8 * Finset.sum (Icc 1 X) f := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ <= 16 * Finset.sum (Icc 1 (2 * X)) f := by linarith

theorem nyman_high_coefficient_weighted_obstruction
    (N H X : Nat) (c : Nat -> Real) (hN : 2 <= N) (hHN : H <= N)
    (hXH : 2 * X <= H)
    (hlow : ∀ k, k ∈ Icc 2 N -> k <= H ->
      c k = nymanLogCoefficient N k) :
    Finset.sum (Icc 1 X) (fun m => nymanWeight m * (2 * nymanPsi m - nymanPsi (2 * m)) ^ 2) <=
      16 * Real.log (N : Real) ^ 2 *
        Finset.sum (Icc 1 (2 * X)) (fun n => nymanWeight n * nymanResidual N c n ^ 2) := by
  have he :
      Finset.sum (Icc 1 X) (fun m => nymanWeight m * (2 * nymanPsi m - nymanPsi (2 * m)) ^ 2) =
        Real.log (N : Real) ^ 2 * Finset.sum (Icc 1 X)
          (fun m => nymanWeight m *
            (nymanResidual N c (2 * m) - 2 * nymanResidual N c m) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmX := (Finset.mem_Icc.mp hm).2
    rw [← nyman_high_coefficient_annihilator N H m c hN hHN hm1 (by omega) hlow]
    ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (nyman_dyadic_weighted_bound X (nymanResidual N c))
    (sq_nonneg (Real.log (N : Real)))
  nlinarith only [hb]

#check nymanLogCoefficient_eq_original
#check nyman_high_coefficient_annihilator
#check nyman_dyadic_weighted_bound
#check nyman_high_coefficient_weighted_obstruction
#print axioms nymanLogCoefficient_eq_original
#print axioms nyman_high_coefficient_annihilator
#print axioms nyman_dyadic_weighted_bound
#print axioms nyman_high_coefficient_weighted_obstruction

end RHLean.Analysis
