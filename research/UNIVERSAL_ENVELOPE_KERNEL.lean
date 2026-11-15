import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Proof.SquareRootAmplificationLogGrowth

/-!
# Finite kernels for the universal historical envelope

The finite Dirichlet-inversion identity below is the discrete version of
ENV-1 in the accompanying research note.  It retains the original Möbius
coefficients.  The Abel identity has no assumed arithmetic estimate.

The cutoff kernel uses `max 1 (u / n)`.  When its potential vanishes at one,
this is exactly the usual sum over `n ≤ u`; the clipped presentation makes
continuity at integer cutoffs explicit.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators Topology
open Finset Set Filter

namespace RHLean.Analysis.UniversalEnvelope

/-- Dirichlet inversion, with an arbitrary weight on the product. -/
theorem moebius_product_kernel_inversion (F : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
      ∑ n ∈ Finset.Icc 1 (N / d), F (d * n)) = F 1 := by
  classical
  calc
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
        ∑ n ∈ Finset.Icc 1 (N / d), F (d * n)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / d),
        (((μ d : ℤ) : ℂ)) * F (d * n) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ p ∈ k.divisorsAntidiagonal,
        (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2) :=
      (sum_Icc_divisorsAntidiagonal_eq_sum_div
        (fun d n => (((μ d : ℤ) : ℂ)) * F (d * n)) N).symm
    _ = ∑ k ∈ Finset.Icc 1 N, (if k = 1 then 1 else 0 : ℂ) * F k := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ p ∈ k.divisorsAntidiagonal,
            (((μ p.1 : ℤ) : ℂ)) * F (p.1 * p.2)) =
          ∑ p ∈ k.divisorsAntidiagonal,
            (((μ p.1 : ℤ) : ℂ)) * F k := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
        _ = (∑ d ∈ k.divisors, (((μ d : ℤ) : ℂ))) * F k := by
          rw [← Finset.sum_mul]
          congr 1
          exact Nat.sum_divisorsAntidiagonal (f := fun d _ => (((μ d : ℤ) : ℂ)))
        _ = (if k = 1 then 1 else 0 : ℂ) * F k := by
          rw [sum_divisors_moebius_eq_ite]
    _ = F 1 := by simp [hN]

/-- The potential summed over the exact positive integer cutoff. -/
def divisorKernel (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, F (u / n)

/-- The real-argument form of finite Möbius inversion. -/
theorem divisorKernel_inversion (F : ℝ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, (((μ d : ℤ) : ℂ)) *
      divisorKernel F ((N : ℝ) / d)) = F N := by
  have h := moebius_product_kernel_inversion
    (fun k => F ((N : ℝ) / k)) hN
  simpa only [divisorKernel, Nat.floor_div_natCast, Nat.floor_natCast,
    Nat.cast_mul, div_div, Nat.cast_one, div_one] using h

/-- A fixed finite cutoff, continuously clipped at the lower endpoint. -/
def clippedKernel (N : ℕ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, F (max 1 (u / n))

theorem clippedKernel_eq_divisorKernel {F : ℝ → ℂ} (hF : F 1 = 0)
    {N : ℕ} {u : ℝ} (hu : 0 ≤ u) (hN : ⌊u⌋₊ ≤ N) :
    clippedKernel N F u = divisorKernel F u := by
  classical
  unfold clippedKernel divisorKernel
  symm
  calc
    (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, F (u / n)) =
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, F (max 1 (u / n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnu : (n : ℝ) ≤ u :=
        (Nat.le_floor_iff hu).mp (Finset.mem_Icc.mp hn).2
      rw [max_eq_right ((le_div_iff₀ hnpos).mpr (by simpa using hnu))]
    _ = ∑ n ∈ Finset.Icc 1 N, F (max 1 (u / n)) := by
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
          (Finset.mem_Icc.mp hn).2.trans hN⟩
      · intro n hn hnnot
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have hfloor : ⌊u⌋₊ < n := by
          by_contra h
          exact hnnot (Finset.mem_Icc.mpr ⟨hn1, by omega⟩)
        have hun : u < (n : ℝ) := (Nat.floor_lt hu).mp hfloor
        rw [max_eq_left (le_of_lt ((div_lt_one hnpos).mpr hun)), hF]

/-- A complex-valued finite Abel identity with the inclusive Mertens prefix. -/
theorem abel_Icc (a w : ℕ → ℂ) : ∀ N : ℕ,
    (∑ n ∈ Finset.Icc 1 N, a n * w n) =
      (∑ n ∈ Finset.Icc 1 N, a n) * w N +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n, a k) * (w n - w (n + 1)) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      by_cases hN : N = 0
      · subst N
        simp
      · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
          Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
        ring

/-- Retain the signed prefix until after the exact Abel identity. -/
theorem moebius_kernel_norm_le (w : ℕ → ℂ) (b : ℕ → ℝ) (N : ℕ)
    (hterminal : w N = 0)
    (hincrement : ∀ n ∈ Finset.Ico 1 N, ‖w n - w (n + 1)‖ ≤ b n) :
    ‖∑ n ∈ Finset.Icc 1 N, (((μ n : ℤ) : ℂ)) * w n‖ ≤
      ∑ n ∈ Finset.Ico 1 N, ‖mertensSummatory n‖ * b n := by
  rw [abel_Icc, hterminal, mul_zero, zero_add]
  calc
    ‖∑ n ∈ Finset.Ico 1 N,
        (∑ k ∈ Finset.Icc 1 n, (((μ k : ℤ) : ℂ))) * (w n - w (n + 1))‖ ≤
      ∑ n ∈ Finset.Ico 1 N,
        ‖(∑ k ∈ Finset.Icc 1 n, (((μ k : ℤ) : ℂ))) * (w n - w (n + 1))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico 1 N, ‖mertensSummatory n‖ * b n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mertensSummatory_eq_sum_Icc, norm_mul]
      exact mul_le_mul_of_nonneg_left (hincrement n hn) (norm_nonneg _)

/-- Combining inversion and Abel leaves only the actual historical Mertens
prefixes and increments of the complete divisor kernel. -/
theorem potential_norm_le_of_kernel_increments {F : ℝ → ℂ} (hF : F 1 = 0)
    {N : ℕ} (hN : 1 ≤ N) (b : ℕ → ℝ)
    (hincrement : ∀ n ∈ Finset.Ico 1 N,
      ‖divisorKernel F ((N : ℝ) / n) -
        divisorKernel F ((N : ℝ) / (n + 1))‖ ≤ b n) :
    ‖F N‖ ≤ ∑ n ∈ Finset.Ico 1 N, ‖mertensSummatory n‖ * b n := by
  rw [← divisorKernel_inversion F hN]
  apply moebius_kernel_norm_le
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp [divisorKernel, hN0, hF]
  · simpa only [Nat.cast_add, Nat.cast_one] using hincrement

theorem clippedKernel_continuous {F : ℝ → ℂ}
    (hF : ContinuousOn F (Set.Ici 1)) (N : ℕ) :
    Continuous (clippedKernel N F) := by
  unfold clippedKernel
  apply continuous_finsetSum
  intro n hn
  exact hF.comp_continuous (continuous_const.max (continuous_id.div_const _))
    (fun u => le_max_left _ _)

/-- At a cutoff, use the derivative from the right.  The newly entering term
is included, so no differentiability claim at an integer kink is needed. -/
theorem clipped_term_hasDerivWithinAt {F κ : ℝ → ℂ}
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 1 ≤ u) :
    HasDerivWithinAt (fun v : ℝ => F (max 1 (v / n)))
      (if (n : ℝ) ≤ u then κ (u / n) / (u : ℂ) else 0) (Set.Ici u) u := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast (by linarith : u ≠ 0)
  by_cases hnu : (n : ℝ) ≤ u
  · rw [if_pos hnu]
    have hv : 1 ≤ u / n := (le_div_iff₀ hnpos).mpr (by simpa using hnu)
    have hd := (hF (u / n) hv).scomp u ((hasDerivAt_id u).div_const (n : ℝ))
    have hd' : HasDerivAt (fun v : ℝ => F (v / n))
        (κ (u / n) / (u : ℂ)) u := by
      have hcoef : (1 / (n : ℝ)) • (κ (u / n) / ((u / n : ℝ) : ℂ)) =
          κ (u / n) / (u : ℂ) := by
        simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_natCast]
        field_simp [hn0, hu0]
      simpa only [Function.comp_apply, hcoef] using hd
    apply hd'.hasDerivWithinAt.congr_of_mem
    · intro v hvu
      rw [max_eq_right ((le_div_iff₀ hnpos).mpr (by simpa using hnu.trans hvu))]
    · exact le_rfl
  · rw [if_neg hnu]
    have hun : u < (n : ℝ) := lt_of_not_ge hnu
    have heq : (fun v : ℝ => F (max 1 (v / n))) =ᶠ[𝓝 u] fun _ => F 1 := by
      filter_upwards [Iio_mem_nhds hun] with v hv
      rw [max_eq_left (le_of_lt ((div_lt_one hnpos).mpr hv))]
    exact ((hasDerivAt_const u (F 1)).congr_of_eventuallyEq heq).hasDerivWithinAt

theorem clippedKernel_hasDerivWithinAt {F κ : ℝ → ℂ}
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {N : ℕ} {u : ℝ} (hu : 1 ≤ u) (huN : u ≤ N) :
    HasDerivWithinAt (clippedKernel N F)
      (divisorKernel κ u / (u : ℂ)) (Set.Ici u) u := by
  classical
  have hfloor : ⌊u⌋₊ ≤ N := Nat.floor_le_of_le huN
  have hfilter : (Finset.Icc 1 N).filter (fun n : ℕ => (n : ℝ) ≤ u) =
      Finset.Icc 1 ⌊u⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn, _⟩, hnu⟩
      exact ⟨hn, (Nat.le_floor_iff (by linarith)).mpr hnu⟩
    · rintro ⟨hn, hnu⟩
      exact ⟨⟨hn, hnu.trans hfloor⟩,
        (Nat.le_floor_iff (by linarith)).mp hnu⟩
  have hd := HasDerivWithinAt.fun_sum (u := Finset.Icc 1 N)
    (fun n hn => clipped_term_hasDerivWithinAt hF (Finset.mem_Icc.mp hn).1 hu)
  have hcoef : (∑ n ∈ Finset.Icc 1 N,
      if (n : ℝ) ≤ u then κ (u / n) / (u : ℂ) else 0) =
      divisorKernel κ u / (u : ℂ) := by
    rw [← Finset.sum_filter, hfilter, ← Finset.sum_div]
    rfl
  simpa only [clippedKernel, hcoef] using hd

/-- A bounded complete derivative kernel pays the reciprocal increments of
the integrated divisor kernel.  The constant is uniform before `N` and `n`.
-/
theorem divisorKernel_increment_norm_le {F κ : ℝ → ℂ}
    (hFone : F 1 = 0)
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ u : ℝ, 1 ≤ u → ‖divisorKernel κ u‖ ≤ C)
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    ‖divisorKernel F ((N : ℝ) / n) -
      divisorKernel F ((N : ℝ) / (n + 1))‖ ≤ C / n := by
  let a : ℝ := (N : ℝ) / (n + 1)
  let b : ℝ := (N : ℝ) / n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha : 1 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    norm_cast
    omega
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_left hNpos.le hnpos (by linarith)
  have hbN : b ≤ N := by
    dsimp [b]
    apply (div_le_iff₀ hnpos).mpr
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hcont : Continuous (clippedKernel N F) :=
    clippedKernel_continuous (fun v hv => (hF v hv).continuousAt.continuousWithinAt) N
  have hderiv : ∀ u ∈ Set.Ico a b,
      HasDerivWithinAt (clippedKernel N F)
        (divisorKernel κ u / (u : ℂ)) (Set.Ici u) u := by
    intro u hu
    exact clippedKernel_hasDerivWithinAt hF (ha.trans hu.1) (hu.2.le.trans hbN)
  have hbound : ∀ u ∈ Set.Ico a b,
      ‖divisorKernel κ u / (u : ℂ)‖ ≤ C / a := by
    intro u hu
    have hu1 : 1 ≤ u := ha.trans hu.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < u)]
    exact (div_le_div_of_nonneg_right (hκ u hu1) (by linarith)).trans
      (div_le_div_of_nonneg_left hC (by linarith) hu.1)
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    hcont.continuousOn hderiv hbound b ⟨hab, le_rfl⟩
  have hea : clippedKernel N F a = divisorKernel F a :=
    clippedKernel_eq_divisorKernel hFone (by linarith) (Nat.floor_le_of_le (hab.trans hbN))
  have heb : clippedKernel N F b = divisorKernel F b :=
    clippedKernel_eq_divisorKernel hFone (by linarith) (Nat.floor_le_of_le hbN)
  rw [hea, heb] at h
  have hscale : C / a * (b - a) = C / n := by
    dsimp [a, b]
    field_simp [hNpos.ne', hnpos.ne', (by positivity : (n : ℝ) + 1 ≠ 0)]
    <;> ring
  rw [hscale] at h
  exact h

theorem potential_norm_le_reciprocal_history {F κ : ℝ → ℂ}
    (hFone : F 1 = 0)
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ u : ℝ, 1 ≤ u → ‖divisorKernel κ u‖ ≤ C)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖F N‖ ≤ ∑ n ∈ Finset.Ico 1 N, ‖mertensSummatory n‖ * (C / n) := by
  apply potential_norm_le_of_kernel_increments hFone hN (fun n => C / n)
  intro n hn
  exact divisorKernel_increment_norm_le hFone hF hC hκ
    (Finset.mem_Ico.mp hn).1 (Finset.mem_Ico.mp hn).2

private theorem sqrt_succ_div_le_telescope {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) / n ≤
      4 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have ha := Real.sq_sqrt hnpos.le
  have hb := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hd : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hproduct :
      (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) + 1)) *
        (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) = 1 := by
    nlinarith
  have hbound : Real.sqrt ((n : ℝ) + 1) *
      (Real.sqrt (n : ℝ) + Real.sqrt ((n : ℝ) + 1)) ≤ 4 * (n : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]
  have hmul := mul_le_mul_of_nonneg_right hbound hd
  rw [mul_assoc, hproduct, mul_one] at hmul
  apply (div_le_iff₀ hnpos).mpr
  nlinarith

/-- A finite square-root telescoping bound; no asymptotic integral estimate
is needed to pay the complete historical prefix. -/
theorem sum_sqrt_succ_div_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 N, Real.sqrt ((n : ℝ) + 1) / n) ≤
      4 * Real.sqrt (N : ℝ) := by
  have htelescope : ∀ M : ℕ, 1 ≤ M →
      (∑ n ∈ Finset.Ico 1 M,
        (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))) =
        Real.sqrt (M : ℝ) - 1 := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
        rw [Finset.sum_Ico_succ_top hM, ih]
        push_cast
        ring
  calc
    (∑ n ∈ Finset.Ico 1 N, Real.sqrt ((n : ℝ) + 1) / n) ≤
      ∑ n ∈ Finset.Ico 1 N,
        4 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact sqrt_succ_div_le_telescope (Finset.mem_Ico.mp hn).1
    _ = 4 * (Real.sqrt (N : ℝ) - 1) := by
      rw [← Finset.mul_sum, htelescope N hN]
    _ ≤ 4 * Real.sqrt (N : ℝ) := by linarith

theorem mertens_norm_le_historical_sqrt {N n : ℕ} (hN : 1 ≤ N) (hn : n < N) :
    ‖mertensSummatory n‖ ≤
      2 * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
        Real.sqrt ((n : ℝ) + 1) := by
  let K := RHLean.Proof.squareRootHistoricalK N
  have hK : 1 ≤ K := RHLean.Proof.squareRootHistoricalK_one_le hN
  have hK0 : 0 ≤ K := by linarith
  have hcenter := (RHLean.Proof.squareRootHistoricalK_envelope N).2 n hn
  push_cast at hcenter
  change ((RHLean.Proof.mertensSummatoryInt n : ℝ) - 1) ^ 2 ≤
    K * ((n : ℝ) + 1) at hcenter
  have hsqK := Real.sq_sqrt hK0
  have hsqn := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
  have hsK : 1 ≤ Real.sqrt K := (Real.one_le_sqrt).mpr hK
  have hsn : 1 ≤ Real.sqrt ((n : ℝ) + 1) :=
    (Real.one_le_sqrt).mpr (by positivity)
  have hA : 1 ≤ Real.sqrt K * Real.sqrt ((n : ℝ) + 1) :=
    one_le_mul_of_one_le_of_one_le hsK hsn
  have hAsq : (Real.sqrt K * Real.sqrt ((n : ℝ) + 1)) ^ 2 =
      K * ((n : ℝ) + 1) := by
    rw [mul_pow, hsqK, hsqn]
  have hcenterAbs : |(RHLean.Proof.mertensSummatoryInt n : ℝ) - 1| ≤
      Real.sqrt K * Real.sqrt ((n : ℝ) + 1) := by
    nlinarith [sq_abs ((RHLean.Proof.mertensSummatoryInt n : ℝ) - 1),
      abs_nonneg ((RHLean.Proof.mertensSummatoryInt n : ℝ) - 1)]
  rw [← RHLean.Proof.mertensSummatoryInt_cast, Complex.norm_intCast]
  have htriangle := abs_add_le ((RHLean.Proof.mertensSummatoryInt n : ℝ) - 1) 1
  norm_num only [sub_add_cancel, abs_one] at htriangle
  dsimp [K] at hcenterAbs hA
  nlinarith

/-- The complete kernel bound controls the potential by the actual strict
history, with an explicit (deliberately coarse) absolute constant. -/
theorem potential_norm_le_historical_sqrt {F κ : ℝ → ℂ}
    (hFone : F 1 = 0)
    (hF : ∀ v : ℝ, 1 ≤ v → HasDerivAt F (κ v / (v : ℂ)) v)
    {C : ℝ} (hC : 0 ≤ C)
    (hκ : ∀ u : ℝ, 1 ≤ u → ‖divisorKernel κ u‖ ≤ C)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖F N‖ ≤ 8 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
      Real.sqrt (N : ℝ) := by
  have hhist := potential_norm_le_reciprocal_history hFone hF hC hκ hN
  calc
    ‖F N‖ ≤ ∑ n ∈ Finset.Ico 1 N, ‖mertensSummatory n‖ * (C / n) := hhist
    _ ≤ ∑ n ∈ Finset.Ico 1 N,
        (2 * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
          Real.sqrt ((n : ℝ) + 1)) * (C / n) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (mertens_norm_le_historical_sqrt hN (Finset.mem_Ico.mp hn).2)
        (div_nonneg hC (Nat.cast_nonneg _))
    _ = (2 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK N)) *
        (∑ n ∈ Finset.Ico 1 N, Real.sqrt ((n : ℝ) + 1) / n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (2 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK N)) *
        (4 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_sqrt_succ_div_le hN) (by positivity)
    _ = 8 * C * Real.sqrt (RHLean.Proof.squareRootHistoricalK N) *
        Real.sqrt (N : ℝ) := by ring

end RHLean.Analysis.UniversalEnvelope
