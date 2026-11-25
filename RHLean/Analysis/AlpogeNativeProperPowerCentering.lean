import RHLean.Analysis.AlpogeNativeSquareCandidateCapacity
import RHLean.Analysis.AlpogeNativeGzRealInterpolation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Uniform centering of the weighted proper-prime-power sector

The prefix discrepancies of the nonprime von Mangoldt mass are bounded by
Chebyshev's square-root estimate. A discrete Abel comparison retains the
endpoint of the original kernel and gives the same constant at every cutoff.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators
open Filter

namespace RHLean.Analysis

/-- The von Mangoldt atom supported on proper prime powers, with its original weight. -/
def nativeProperPowerAtom (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

/-- The centering coefficient is the full reciprocal series over positive proper powers. -/
def nativeProperPowerCenter : ℝ :=
  ∑' k : ℕ, nativeProperPowerAtom (k + 1) / ((k + 1 : ℕ) : ℝ)

private def mass (M : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 M, nativeProperPowerAtom n

private def recipPrefix (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, nativeProperPowerAtom n / (n : ℝ)

private theorem atom_nonneg (n : ℕ) : 0 ≤ nativeProperPowerAtom n := by
  by_cases h : n.Prime <;> simp [nativeProperPowerAtom, h, ArithmeticFunction.vonMangoldt_nonneg]

private theorem mass_chebyshev (M : ℕ) : mass M = Chebyshev.psi M - Chebyshev.theta M := by
  have hset : Finset.Ioc 0 M = Finset.Icc 1 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, hset, Finset.sum_filter]
  unfold mass
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : n.Prime <;> simp [nativeProperPowerAtom, h]

private theorem mass_succ (M : ℕ) : mass (M + 1) = mass M + nativeProperPowerAtom (M + 1) :=
  Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1) _

private theorem recipPrefix_succ (M : ℕ) : recipPrefix (M + 1) =
    recipPrefix M + nativeProperPowerAtom (M + 1) / ((M + 1 : ℕ) : ℝ) :=
  Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1) _

private theorem recipPrefix_mono : Monotone recipPrefix := by
  apply monotone_nat_of_le_succ
  intro M
  rw [recipPrefix_succ]
  exact le_add_of_nonneg_right (div_nonneg (atom_nonneg _) (Nat.cast_nonneg _))

private theorem recipPrefix_range (M : ℕ) :
    (∑ k ∈ Finset.range M, nativeProperPowerAtom (k + 1) / ((k + 1 : ℕ) : ℝ)) = recipPrefix M := by
  induction M with
  | zero => simp [recipPrefix]
  | succ M ih => rw [Finset.sum_range_succ, ih, recipPrefix_succ]

private theorem proper_capacity_eq (N : ℕ) :
    nativeSquareProperPowerCapacity N = (N : ℝ) * recipPrefix N - mass N := by
  unfold nativeSquareProperPowerCapacity nativeSquareCandidateKernel recipPrefix mass
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : n.Prime <;> simp [nativeProperPowerAtom, h] <;> ring

private theorem sqrt_kernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt x * (1 / x - 1 / y) ≤ 2 * (1 / Real.sqrt x - 1 / Real.sqrt y) := by
  let a := Real.sqrt x
  let b := Real.sqrt y
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr hy
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = y := Real.sq_sqrt hy.le
  have he : 2 * (1 / a - 1 / b) - a * (1 / x - 1 / y) =
      (b - a) ^ 2 / (a * b ^ 2) := by
    rw [← ha2, ← hb2]
    field_simp [ha.ne', hb.ne'] <;> ring
  have hn : 0 ≤ (b - a) ^ 2 / (a * b ^ 2) := by positivity
  change a * (1 / x - 1 / y) ≤ 2 * (1 / a - 1 / b)
  linarith only [he, hn]

private def potential (C : ℝ) (N M : ℕ) : ℝ :=
  (N : ℝ) * recipPrefix M - nativeSquareProperPowerCapacity N -
    (N : ℝ) * (mass M / (M : ℝ)) + 2 * C * (N : ℝ) / Real.sqrt (M : ℝ)

private theorem finite_proper_power_error (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ k : ℕ, mass k ≤ C * Real.sqrt (k : ℝ)) {N : ℕ} (hN : 1 ≤ N)
    (M : ℕ) (hM : N ≤ M) :
    0 ≤ (N : ℝ) * recipPrefix M - nativeSquareProperPowerCapacity N ∧
      (N : ℝ) * recipPrefix M - nativeSquareProperPowerCapacity N ≤ 2 * C * Real.sqrt (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpot : ∀ k ≥ N, potential C N k ≤ 2 * C * Real.sqrt (N : ℝ) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      have hs := Real.sqrt_pos.mpr hn
      have he : (N : ℝ) / Real.sqrt (N : ℝ) = Real.sqrt (N : ℝ) :=
        (div_eq_iff hs.ne').mpr (Real.mul_self_sqrt hn.le).symm
      have hc : (N : ℝ) * (mass N / (N : ℝ)) = mass N := by field_simp [hn.ne']
      unfold potential
      rw [proper_capacity_eq, hc, mul_div_assoc, he]
      linarith
    | succ k hk ih =>
      have hx : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hy : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hxy : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
      have hd : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) :=
        sub_nonneg.mpr (one_div_le_one_div_of_le hx hxy)
      have hgain : mass k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
          2 * C * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by
        calc
          _ ≤ C * Real.sqrt (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (hB k) hd
          _ ≤ _ := by
            have hh := mul_le_mul_of_nonneg_left (sqrt_kernel hx hy) hC
            linarith only [hh]
      have he : potential C N (k + 1) - potential C N k =
          (N : ℝ) * (mass k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))) -
            (N : ℝ) * (2 * C * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ))) := by
        unfold potential
        rw [mass_succ, recipPrefix_succ]
        ring
      linarith only [ih, he, mul_le_mul_of_nonneg_left hgain hn.le]
  have hm : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hs := Real.sqrt_pos.mpr hm
  have hquot : mass M / (M : ℝ) ≤ C / Real.sqrt (M : ℝ) := by
    rw [div_le_div_iff₀ hm hs]
    calc
      _ ≤ (C * Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ) := mul_le_mul_of_nonneg_right (hB M) hs.le
      _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hm.le]
  have hM0 : 0 ≤ mass N := Finset.sum_nonneg fun n _ => atom_nonneg n
  constructor
  · rw [proper_capacity_eq]
    linarith only [mul_le_mul_of_nonneg_left (recipPrefix_mono hM) hn.le, hM0]
  · have h := hpot M hM
    unfold potential at h
    have hz : 0 ≤ (N : ℝ) * (C / Real.sqrt (M : ℝ)) := by positivity
    have hboundary : (N : ℝ) * (mass M / (M : ℝ)) ≤
        2 * C * (N : ℝ) / Real.sqrt (M : ℝ) := calc
      _ ≤ (N : ℝ) * (C / Real.sqrt (M : ℝ)) := mul_le_mul_of_nonneg_left hquot hn.le
      _ ≤ (N : ℝ) * (C / Real.sqrt (M : ℝ)) + (N : ℝ) * (C / Real.sqrt (M : ℝ)) :=
        le_add_of_nonneg_right hz
      _ = _ := by ring
    calc
      _ = (N : ℝ) * recipPrefix M - nativeSquareProperPowerCapacity N -
          (N : ℝ) * (mass M / (M : ℝ)) + (N : ℝ) * (mass M / (M : ℝ)) :=
        (sub_add_cancel _ _).symm
      _ ≤ _ := (add_le_add le_rfl hboundary).trans h

/-- The complete nonprime von Mangoldt reciprocal series converges. Its centered
weighted contribution lies between zero and `2*C*sqrt N` at every positive
integer cutoff, for one Chebyshev constant independent of the cutoff. -/
theorem nativeProperPowerCenter_summable_and_error :
    Summable (fun k : ℕ => nativeProperPowerAtom (k + 1) / ((k + 1 : ℕ) : ℝ)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      0 ≤ (N : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity N ∧
      (N : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity N ≤ 2 * C * Real.sqrt (N : ℝ) := by
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := |D|
  have hC : 0 ≤ C := abs_nonneg _
  have hB (M : ℕ) : mass M ≤ C * Real.sqrt (M : ℝ) :=
    (mass_chebyshev M).le.trans ((hD _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)))
  have hpart (M : ℕ) : recipPrefix M ≤ nativeSquareProperPowerCapacity 1 + 2 * C := by
    cases M with
    | zero =>
      have hz : recipPrefix 0 = 0 := by simp [recipPrefix]
      rw [hz]
      linarith only [nativeSquareProperPowerCapacity_nonneg 1, hC]
    | succ k =>
      have hh := (finite_proper_power_error C hC hB (by decide : 1 ≤ 1) (k + 1) (by omega)).2
      norm_num at hh
      linarith only [hh]
  have hsum := summable_of_sum_range_le
    (fun k : ℕ => div_nonneg (atom_nonneg (k + 1)) (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ _))
    (fun M => (recipPrefix_range M).le.trans (hpart M))
  refine ⟨hsum, C, hC, ?_⟩
  intro N hN
  have hlim : Tendsto recipPrefix atTop (nhds nativeProperPowerCenter) := by
    simpa only [recipPrefix_range, nativeProperPowerCenter] using hsum.hasSum.tendsto_sum_nat
  have ht : Tendsto (fun M => (N : ℝ) * recipPrefix M - nativeSquareProperPowerCapacity N)
      atTop (nhds ((N : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity N)) :=
    (tendsto_const_nhds.mul hlim).sub_const _
  constructor
  · apply ge_of_tendsto ht
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (finite_proper_power_error C hC hB hN M hM).1
  · apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (finite_proper_power_error C hC hB hN M hM).2


/-- The same centering constant pays the proper-power error throughout every
square-clock window, including each upper cutoff `R^2 - 1`. -/
theorem nativeProperPowerCenter_square_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℕ, 2 ≤ R →
      0 ≤ ((R ^ 2 - 1 : ℕ) : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity (R ^ 2 - 1) ∧
      ((R ^ 2 - 1 : ℕ) : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity (R ^ 2 - 1) ≤ K * R := by
  obtain ⟨C, hC, hb⟩ := nativeProperPowerCenter_summable_and_error.2
  refine ⟨2 * C, by positivity, ?_⟩
  intro R hR
  have h2 : (2 : ℕ) ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hR 2
  have hN : 1 ≤ R ^ 2 - 1 := by omega
  have hs : Real.sqrt ((R ^ 2 - 1 : ℕ) : ℝ) ≤ (R : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast Nat.sub_le (R ^ 2) 1
  exact ⟨(hb _ hN).1, (hb _ hN).2.trans (mul_le_mul_of_nonneg_left hs (by positivity))⟩


/-- The remaining prime sum uses only first powers above the arithmetic
cutoff. The low first powers and every higher power retain their original
Euler main terms. -/
def nativeHighFirstPrimeCenter (N z : ℕ) : ℝ :=
  (∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ z), nativeSquareCandidateWeight N p) +
    (N : ℝ) * (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (p : ℝ)) -
    (N : ℝ) * Real.log (N : ℝ) + (1 + Real.eulerMascheroniConstant + nativeProperPowerCenter) * N

theorem nativeHighFirstPrimeCenter_sub_gz (N z : ℕ) (hz : z ≤ N) :
    nativeHighFirstPrimeCenter N z - nativeAlpogeGz N = Chebyshev.theta (z : ℝ) +
      ((N : ℝ) * nativeProperPowerCenter - nativeSquareProperPowerCapacity N) := by
  classical
  have hl : (Nat.primesLE N).filter (fun p => p ≤ z) = Nat.primesLE z := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, h⟩
      exact ⟨h, hp⟩
    · rintro ⟨h, hp⟩
      exact ⟨⟨h.trans hz, hp⟩, h⟩
  have htheta : Chebyshev.theta (z : ℝ) = ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast, Nat.primesLE_eq_filter_Ioc_zero]
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Nat.primesLE N)
    (p := fun p => p ≤ z) (f := nativeSquareCandidateWeight N)
  rw [hl] at hsplit
  have hlow : (N : ℝ) * (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ Nat.primesLE z, nativeSquareCandidateWeight N p = Chebyshev.theta (z : ℝ) := by
    rw [htheta, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by
      unfold nativeSquareCandidateWeight nativeSquareCandidateKernel
      ring
  have hprime := nativeAlpogeGz_eq_candidateCapacity_sub_removal (Nat.primesLE N) N
    (by rw [Nat.primesLE_eq_filter_Icc_one]; exact Finset.filter_subset _ _)
    (fun p hp hpr => Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp).2, hpr⟩)
  have hnone : (Nat.primesLE N).filter (fun p => ¬ p.Prime) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p h
    obtain ⟨hp, hn⟩ := Finset.mem_filter.mp h
    exact hn (Nat.mem_primesLE.mp hp).2
  unfold nativeSquareCandidateCapacity nativeSquareCompositeRemoval at hprime
  rw [hnone, Finset.sum_empty, sub_zero] at hprime
  unfold nativeHighFirstPrimeCenter
  rw [hprime]
  linear_combination hsplit + hlow

theorem nativeHighFirstPrimeCenter_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N z : ℕ), 1 ≤ N → z ≤ N →
      0 ≤ nativeHighFirstPrimeCenter N z - nativeAlpogeGz N ∧
      nativeHighFirstPrimeCenter N z - nativeAlpogeGz N ≤
        K * Real.sqrt (N : ℝ) + Real.log 4 * z := by
  obtain ⟨C, hC, h⟩ := nativeProperPowerCenter_summable_and_error.2
  refine ⟨2 * C, by positivity, ?_⟩
  intro N z hN hz
  rw [nativeHighFirstPrimeCenter_sub_gz N z hz]
  have hθ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg z : 0 ≤ (z : ℝ))
  exact ⟨add_nonneg (Chebyshev.theta_nonneg _) (h N hN).1, by linarith only [hθ, (h N hN).2]⟩

/-- Subtracting the exact low-prime boundary makes the real comparison
uniform even for changing cutoffs. In the upper bound for the full source
only the original fractional-step cost remains. -/
theorem nativeHighFirstPrimeCenter_real_comparison :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : ℝ) (z : ℕ), 1 ≤ x → z ≤ ⌊x⌋₊ →
      alpogeNativeGzArithmetic x ≤ nativeHighFirstPrimeCenter ⌊x⌋₊ z - Chebyshev.theta z +
        nativeAlpogeSafeSlope * (x - ⌊x⌋₊) ∧
      nativeHighFirstPrimeCenter ⌊x⌋₊ z - Chebyshev.theta z ≤ alpogeNativeGzArithmetic x +
        (K * Real.sqrt x + (alpogeGzInterpolationSlope + 1)) := by
  obtain ⟨C, hC, h⟩ := nativeProperPowerCenter_summable_and_error.2
  have hK : 0 ≤ 2 * C := by positivity
  refine ⟨2 * C, hK, ?_⟩
  intro x z hx hz
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hn : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hid := nativeHighFirstPrimeCenter_sub_gz ⌊x⌋₊ z hz
  obtain ⟨hlow, hhigh⟩ := h ⌊x⌋₊ hn
  have hfloorLo := (abs_le.mp (alpogeNativeGzArithmetic_sub_floor_abs_le x hx)).1
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hx0)) hK
  constructor
  · linarith only [hid, hlow, alpogeNativeGzArithmetic_le_floor x hx]
  · linarith only [hid, hhigh, hfloorLo, hroot]

end RHLean.Analysis
end
