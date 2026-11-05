import «research.NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104»

/-!
Exact finite source return for 20261104-analytic-1/P4-P5 and its head, independently
accepted with scope in 20261104-referee-9. The correction is kept arbitrary:
its reciprocal-moment defect is displayed, never silently discarded.
The two-band solver below verifies the finite moment equations. No infinite
norm estimate, Mellin consumer, new zero-free region, or RH claim is made.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace RHLean.Analysis

def nymanFlatScale (N H : Nat) : Real := Real.log N - Real.log H

def nymanFlatKernel (N H k : Nat) : Real :=
  nymanLogKernel N k - if k <= H then nymanLogKernel H k else 0

def nymanFlatCoefficient (N H : Nat) (h : Nat -> Real) (k : Nat) : Real :=
  (h k - nymanFlatKernel N H k) / nymanFlatScale N H

def nymanFlatMoment (N H : Nat) : Real :=
  Finset.sum (Icc 1 N) (fun k => nymanFlatKernel N H k / (k : Real))

def nymanCorrectionMoment (N : Nat) (h : Nat -> Real) : Real :=
  Finset.sum (Icc 2 N) (fun k => h k / (k : Real))

def nymanLogTail (B m : Nat) : Real :=
  Finset.sum (Ioc B m) (fun k => nymanLogKernel B k * ((m / k : Nat) : Real))

def nymanCorrectionFloor (N : Nat) (h : Nat -> Real) (m : Nat) : Real :=
  Finset.sum (Icc 2 N) (fun k => h k * ((m / k : Nat) : Real))

theorem nymanFlatScale_pos (N H : Nat) (hH : 1 <= H) (hHN : H < N) :
    0 < nymanFlatScale N H := by
  unfold nymanFlatScale
  exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast (show 0 < H by omega))
    (by exact_mod_cast hHN))

theorem nymanFlatKernel_eq_original (N H k : Nat)
    (hN : 1 <= N) (hH : 1 <= H) (hk : 1 <= k) :
    nymanFlatKernel N H k = (ArithmeticFunction.moebius k : Real) *
      Real.log ((N : Real) / (max H k : Nat)) := by
  have hNz : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hHz : (H : Real) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  have hkz : (k : Real) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  by_cases hkH : k <= H
  · simp only [nymanFlatKernel, ite_eq_left hkH, max_eq_left hkH,
      Real.log_div hNz hHz, nymanLogKernel]
    ring
  · simp only [nymanFlatKernel, ite_eq_right hkH, sub_zero,
      max_eq_right (by omega : H <= k), Real.log_div hNz hkz, nymanLogKernel]

theorem nymanFlatKernel_one (N H : Nat) (hH : 1 <= H) :
    nymanFlatKernel N H 1 = nymanFlatScale N H := by
  simp [nymanFlatKernel, nymanLogKernel, nymanFlatScale, hH]

theorem nymanFlatCoefficient_eq_original (N H k : Nat) (h : Nat -> Real)
    (hN : 1 <= N) (hH : 1 <= H) (hk : 1 <= k) :
    nymanFlatCoefficient N H h k =
      (h k - (ArithmeticFunction.moebius k : Real) *
        Real.log ((N : Real) / (max H k : Nat))) /
          Real.log ((N : Real) / (H : Real)) := by
  have hNz : (N : Real) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hHz : (H : Real) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  unfold nymanFlatCoefficient nymanFlatScale
  rw [nymanFlatKernel_eq_original N H k hN hH hk, Real.log_div hNz hHz]

theorem nyman_sum_one_split (N : Nat) (hN : 1 <= N) (f : Nat -> Real) :
    Finset.sum (Icc 1 N) f = f 1 + Finset.sum (Icc 2 N) f := by
  have hset : Icc 1 N = insert 1 (Icc 2 N) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]

theorem nyman_log_floor_full (B m : Nat) (hm : 1 <= m) :
    Finset.sum (Icc 1 m) (fun k => nymanLogKernel B k * ((m / k : Nat) : Real)) =
      Real.log B + nymanPsi m := by
  rw [nyman_sum_mul_floor_eq_divisor_sum]
  have hs : Finset.sum (Icc 1 m) (fun n => Finset.sum n.divisors (nymanLogKernel B)) =
      Finset.sum (Icc 1 m) (fun n => Real.log B * (if n = 1 then 1 else 0) +
        ArithmeticFunction.vonMangoldt n) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact nymanLogKernel_divisor_sum B n (Finset.mem_Icc.mp hn).1
  rw [hs, Finset.sum_add_distrib, <- Finset.mul_sum]
  simp [nymanPsi, Finset.sum_ite_eq', Finset.mem_Icc, hm]

theorem nyman_log_floor_with_tail (B m : Nat) (hB : 1 <= B) (hm : 1 <= m) :
    Finset.sum (Icc 1 B) (fun k => nymanLogKernel B k * ((m / k : Nat) : Real)) =
      Real.log B + nymanPsi m - nymanLogTail B m := by
  by_cases hmB : m <= B
  · have ht : nymanLogTail B m = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    rw [ht, sub_zero]
    exact nymanLogKernel_floor_sum B m hm hmB
  · have hset : Icc 1 m = Icc 1 B ∪ Ioc B m := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
      omega
    have hd : Disjoint (Icc 1 B) (Ioc B m) := by
      apply Finset.disjoint_left.mpr
      intro k hk hb
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hb
      omega
    have hs := nyman_log_floor_full B m hm
    rw [hset, Finset.sum_union hd] at hs
    unfold nymanLogTail
    linarith

theorem nymanFlatKernel_floor_sum (N H m : Nat)
    (hH : 1 <= H) (hHN : H <= N) (hm : 1 <= m) :
    Finset.sum (Icc 1 N) (fun k => nymanFlatKernel N H k * ((m / k : Nat) : Real)) =
      nymanFlatScale N H - nymanLogTail N m + nymanLogTail H m := by
  have hs : Finset.sum (Icc 1 N) (fun k =>
      (if k <= H then nymanLogKernel H k else 0) * ((m / k : Nat) : Real)) =
      Finset.sum (Icc 1 H) (fun k => nymanLogKernel H k * ((m / k : Nat) : Real)) := by
    calc
      _ = Finset.sum (Icc 1 H) (fun k =>
          (if k <= H then nymanLogKernel H k else 0) * ((m / k : Nat) : Real)) := by
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_Icc] at hk ⊢
          omega
        · intro k hk hn
          have hkH : ¬ k <= H := by
            simp only [Finset.mem_Icc] at hk hn
            omega
          simp [hkH]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [(Finset.mem_Icc.mp hk).2]
  unfold nymanFlatKernel
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hs, nyman_log_floor_with_tail N m (hH.trans hHN) hm,
    nyman_log_floor_with_tail H m hH hm]
  unfold nymanFlatScale
  ring

theorem nyman_flat_reciprocal_moment (N H : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) :
    Finset.sum (Icc 2 N) (fun k => nymanFlatCoefficient N H h k / (k : Real)) =
      1 + (nymanCorrectionMoment N h - nymanFlatMoment N H) / nymanFlatScale N H := by
  have hL := (nymanFlatScale_pos N H hH hHN).ne'
  have hs := nyman_sum_one_split N (by omega : 1 <= N)
    (fun k => nymanFlatKernel N H k / (k : Real))
  rw [nymanFlatKernel_one N H hH] at hs
  simp only [Nat.cast_one, div_one] at hs
  have he : Finset.sum (Icc 2 N) (fun k => nymanFlatCoefficient N H h k / (k : Real)) =
      (nymanCorrectionMoment N h -
        Finset.sum (Icc 2 N) (fun k => nymanFlatKernel N H k / (k : Real))) /
          nymanFlatScale N H := by
    unfold nymanCorrectionMoment
    rw [<- Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    unfold nymanFlatCoefficient
    ring
  rw [he]
  unfold nymanFlatMoment
  rw [hs]
  field_simp [hL]
  ring

theorem nyman_flat_complete_return (N H m : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) (hm : 1 <= m) :
    nymanFlatScale N H * nymanResidual N (nymanFlatCoefficient N H h) m =
      (m : Real) * (nymanFlatMoment N H - nymanCorrectionMoment N h) +
        nymanLogTail N m - nymanLogTail H m + nymanCorrectionFloor N h m := by
  have hL := (nymanFlatScale_pos N H hH hHN).ne'
  have hscale : nymanFlatScale N H *
      Finset.sum (Icc 2 N) (fun k => nymanFlatCoefficient N H h k * nymanResidue k m) =
        Finset.sum (Icc 2 N) (fun k =>
          (h k - nymanFlatKernel N H k) * nymanResidue k m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    unfold nymanFlatCoefficient
    field_simp [hL]
  have hsplit : Finset.sum (Icc 2 N) (fun k =>
      (h k - nymanFlatKernel N H k) * nymanResidue k m) =
      (m : Real) * (nymanCorrectionMoment N h -
        Finset.sum (Icc 2 N) (fun k => nymanFlatKernel N H k / (k : Real))) -
        nymanCorrectionFloor N h m +
        Finset.sum (Icc 2 N) (fun k => nymanFlatKernel N H k * ((m / k : Nat) : Real)) := by
    unfold nymanCorrectionMoment nymanCorrectionFloor
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
      <- Finset.sum_sub_distrib, <- Finset.sum_sub_distrib, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [nymanResidue_eq_div_sub_floor k m (by have := (Finset.mem_Icc.mp hk).1; omega)]
    ring
  have hrecip := nyman_sum_one_split N (by omega : 1 <= N)
    (fun k => nymanFlatKernel N H k / (k : Real))
  rw [nymanFlatKernel_one N H hH] at hrecip
  simp only [Nat.cast_one, div_one] at hrecip
  have hfloor := nyman_sum_one_split N (by omega : 1 <= N)
    (fun k => nymanFlatKernel N H k * ((m / k : Nat) : Real))
  rw [nymanFlatKernel_floor_sum N H m hH (Nat.le_of_lt hHN) hm,
    nymanFlatKernel_one N H hH] at hfloor
  simp only [Nat.div_one] at hfloor
  unfold nymanResidual
  rw [mul_sub, hscale, hsplit]
  unfold nymanFlatMoment
  rw [hrecip]
  nlinarith only [hfloor]

theorem nyman_flat_return_of_moment (N H m : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) (hm : 1 <= m)
    (hmoment : nymanCorrectionMoment N h = nymanFlatMoment N H) :
    nymanFlatScale N H * nymanResidual N (nymanFlatCoefficient N H h) m =
      nymanLogTail N m - nymanLogTail H m + nymanCorrectionFloor N h m := by
  rw [nyman_flat_complete_return N H m h hH hHN hm, hmoment]
  ring

theorem nyman_flat_exact_head (N H m : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N) (hm : 1 <= m) (hmH : m <= H)
    (hlow : ∀ k, k ∈ Icc 2 H -> h k = 0)
    (hmoment : nymanCorrectionMoment N h = nymanFlatMoment N H) :
    nymanResidual N (nymanFlatCoefficient N H h) m = 0 := by
  have htail (B : Nat) (hb : m <= B) : nymanLogTail B m = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have := Finset.mem_Ioc.mp hk
    omega
  have hc : nymanCorrectionFloor N h m = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hkH : k <= H
    · rw [hlow k (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hkH⟩)]
      simp
    · simp [Nat.div_eq_of_lt (by omega : m < k)]
  have hr := nyman_flat_return_of_moment N H m h hH hHN hm hmoment
  rw [htail N (by omega), htail H hmH, hc] at hr
  have hL := (nymanFlatScale_pos N H hH hHN).ne'
  exact (mul_eq_zero.mp (by simpa using hr)).resolve_left hL

theorem nyman_flat_head_iff_moment (N H : Nat) (h : Nat -> Real)
    (hH : 1 <= H) (hHN : H < N)
    (hlow : ∀ k, k ∈ Icc 2 H -> h k = 0) :
    (∀ m, 1 <= m -> m <= H ->
      nymanResidual N (nymanFlatCoefficient N H h) m = 0) ↔
      nymanCorrectionMoment N h = nymanFlatMoment N H := by
  constructor
  · intro hhead
    have hr := nyman_flat_complete_return N H 1 h hH hHN (by omega)
    have ht (B : Nat) (hB : 1 <= B) : nymanLogTail B 1 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have := Finset.mem_Ioc.mp hk
      omega
    have hc : nymanCorrectionFloor N h 1 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [Nat.div_eq_of_lt (by have := (Finset.mem_Icc.mp hk).1; omega : 1 < k)]
    rw [hhead 1 (by omega) hH, ht N (by omega), ht H hH, hc] at hr
    norm_num at hr
    linarith
  · intro hmoment m hm hmH
    exact nyman_flat_exact_head N H m h hH hHN hm hmH hlow hmoment

/-- The finite linear system used by the original two-band correction. -/
theorem nyman_two_band_moment_solver (K s1 s2 u v : Real)
    (hK : K ≠ 0) (hs : s1 ≠ s2) :
    let A := (u - s2 * v / K) / (s1 - s2)
    let Z := (s1 * v / K - u) / (s1 - s2)
    A * s1 + Z * s2 = u ∧ K * A + K * Z = v := by
  dsimp
  constructor <;> field_simp [hK, sub_ne_zero.mpr hs] <;> ring

#check nymanFlatKernel_eq_original
#check nymanFlatCoefficient_eq_original
#check nyman_flat_reciprocal_moment
#check nyman_flat_complete_return
#check nyman_flat_return_of_moment
#check nyman_flat_exact_head
#check nyman_flat_head_iff_moment
#check nyman_two_band_moment_solver
#print axioms nymanFlatKernel_eq_original
#print axioms nymanFlatCoefficient_eq_original
#print axioms nyman_flat_reciprocal_moment
#print axioms nyman_flat_complete_return
#print axioms nyman_flat_return_of_moment
#print axioms nyman_flat_exact_head
#print axioms nyman_flat_head_iff_moment
#print axioms nyman_two_band_moment_solver

end RHLean.Analysis
