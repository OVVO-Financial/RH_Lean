import Mathlib
import RHLean.Analysis.MobiusRenewalTelescope
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourMoments

/-!
# PNT-first seam: exact Λ-normalized compensation, historical density model,
# and #915 anchor localization of the cofactor windows

Exact finite arithmetic accompanying the 2026-10-18 PNT-first seven-pass manual
research cycle (`docs/PNT_FIRST_SIGNED_COFACTOR_SEAM_2026_10_18.md`).  At the
square endpoint `X = R^2 - 1` the contract splits `M(X) = S_R - L_R - E_R`.
This file certifies three exact interfaces of that seam.  None is an estimate.

1. **Complete Λ-error hyperbola (classical Landau identity).**
   `Σ_{d ≤ X} (Λ(d) - 1) M(⌊X/d⌋) = -Σ_{n ≤ X} μ(n) log n - 1`.
   It is the Euler-product identity `(1/ζ)' = (1/ζ)(-ζ'/ζ)` (`μ * Λ = -μ log`)
   summed along the hyperbola, combined with `Σ_{d ≤ X} M(⌊X/d⌋) = 1`.  We record
   it — with no novelty claim for the identity itself — because, split at the
   root, its high side `d ≥ R` is the Λ-normalized PNT-first error sector and its
   low side `d ≤ R - 1` is the dual sector.  Their sum is *exactly*
   `-(M(X) log X - ∫_1^X M(t) dt/t) - 1`: a hypothesis bounding the error sector
   alone is, up to the dual sector, a hypothesis on `M(X) log X`.

2. **Historical representation of the Λ-model transport (new identity).**
   With `t_c = ⌊X/c⌋`, the integer-density model of the high-prime transport is
   `L^Λ_R = Σ_{c<R} μ(c) (t_c - (R-1)) = X·J(R-1) + 2 M(R-1) - Φ_R`,
   where `J(N) = Σ_{n=1}^{N-1} M(n)/(n(n+1)) = ∫_1^N M(t) t^{-2} dt` and
   `Φ_R = Σ_{c<R} μ(c) {X/c}`.  Thus the density model is a functional of `M`
   below the root plus `O(R)`.  (The companion paper proof shows, unconditionally,
   that `X·J(R-1)` is not `O(R^{3/2-δ})` for any `δ > 0`; that analytic
   statement uses a zeta zero and is NOT formalized here.)

3. **#915 anchor localization.**  For the original half-run start
   `A = ⌊R/2⌋ + 1`, the top `⌊X/c⌋` of the cofactor-`c` PNT-error window lies in
   a block of the half-run (`A^2 ≤ ⌊X/c⌋`, equivalently `A ≤ ⌊√⌊X/c⌋⌋`) iff
   `c ≤ 3`, for every `R ≥ 13`; every `c ≥ 4` lies below the anchor for every `R`.

No RH-strength, PNT-strength or Mertens hypothesis is used.  These identities
do not bound `E_R`, `S_R - L_R`, `M(X)`, the canonical VF defect, or any
original #915 source; they are not a first-bad payment.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-! ## 1. Landau's identity and the complete Λ-error hyperbola -/

/-- Coefficient identity `Σ_{d ∣ n} μ(d) log d = -Λ(n)`, cast to `ℂ`. -/
theorem pntFirst_moebiusLog_divisorSum_complex (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) * ((Real.log (d : ℝ) : ℝ) : ℂ)) =
      -((Λ n : ℝ) : ℂ) := by
  have h := sum_moebius_log_divisors_eq_neg_vonMangoldt n hn
  have hR : (∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log (d : ℝ)) = -Λ n := by
    rw [← h]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [ArithmeticFunction.intCoe_apply]
  have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg] at hC
  rw [← hC]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  push_cast
  ring

/-- **Landau's identity** `Σ_{d ≤ X} Λ(d) M(⌊X/d⌋) = -Σ_{n ≤ X} μ(n) log n`. -/
theorem pntFirst_landau_vonMangoldt_mertens (X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, ((Λ d : ℝ) : ℂ) * mertensSummatory (X / d)) =
      -∑ n ∈ Finset.Icc 1 X,
        (((μ n : ℤ) : ℂ)) * ((Real.log (n : ℝ) : ℝ) : ℂ) := by
  have h : (∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) * ((Real.log (d : ℝ) : ℝ) : ℂ)) *
          mertensSummatory (X / n)) =
      ∑ a ∈ Finset.Icc 1 X, (((μ a : ℤ) : ℂ)) * ((Real.log (a : ℝ) : ℝ) : ℂ) :=
    sum_convolveOne_mul_mertensSummatory_div
      (fun d => (((μ d : ℤ) : ℂ)) * ((Real.log (d : ℝ) : ℝ) : ℂ)) X
  have hcoef : ∀ n ∈ Finset.Icc 1 X,
      (∑ d ∈ n.divisors, (((μ d : ℤ) : ℂ)) * ((Real.log (d : ℝ) : ℝ) : ℂ)) *
          mertensSummatory (X / n) =
        -(((Λ n : ℝ) : ℂ) * mertensSummatory (X / n)) := by
    intro n hn
    rw [pntFirst_moebiusLog_divisorSum_complex n (Finset.mem_Icc.mp hn).1, neg_mul]
  rw [Finset.sum_congr rfl hcoef, Finset.sum_neg_distrib] at h
  linear_combination -h

/-- **Complete Λ-error hyperbola.**  The PNT-model weight `1` is removed by the
exact unit identity `Σ_{d ≤ X} M(⌊X/d⌋) = 1`; the signed remainder is exactly
`-Σ_{n ≤ X} μ(n) log n - 1`. -/
theorem pntFirst_lambdaError_hyperbola_total (X : ℕ) (hX : 1 ≤ X) :
    (∑ d ∈ Finset.Icc 1 X, (((Λ d : ℝ) : ℂ) - 1) * mertensSummatory (X / d)) =
      -(∑ n ∈ Finset.Icc 1 X,
          (((μ n : ℤ) : ℂ)) * ((Real.log (n : ℝ) : ℝ) : ℂ)) - 1 := by
  have hL := pntFirst_landau_vonMangoldt_mertens X
  have h1 := sum_mertensSummatory_div_eq_one hX
  have hsplit :
      (∑ d ∈ Finset.Icc 1 X, (((Λ d : ℝ) : ℂ) - 1) * mertensSummatory (X / d)) =
        (∑ d ∈ Finset.Icc 1 X, ((Λ d : ℝ) : ℂ) * mertensSummatory (X / d)) -
          ∑ d ∈ Finset.Icc 1 X, mertensSummatory (X / d) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsplit, hL, h1]

/-- Λ-normalized PNT-first error sector at `X = R^2 - 1`: the high side `d ≥ R`
of the complete Λ-error hyperbola.  (By Fubini it equals the contract's cofactor
form `Σ_{c<R} μ(c)[(ψ(t_c) - t_c) - (ψ(R-1) - (R-1))]`.) -/
def pntFirstLambdaError (R : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc (R - 1) (R ^ 2 - 1),
    (((Λ d : ℝ) : ℂ) - 1) * mertensSummatory ((R ^ 2 - 1) / d)

/-- The complementary low side `1 ≤ d ≤ R - 1` (dual sector). -/
def pntFirstLambdaDual (R : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (R - 1),
    (((Λ d : ℝ) : ℂ) - 1) * mertensSummatory ((R ^ 2 - 1) / d)

/-- **Exact root split of the Λ-error hyperbola.**  The error sector and its
dual sum to `-Σ_{n ≤ X} μ(n) log n - 1`; neither sector is controlled
separately by this identity. -/
theorem pntFirstLambdaError_add_dual (R : ℕ) (hR : 2 ≤ R) :
    pntFirstLambdaError R + pntFirstLambdaDual R =
      -(∑ n ∈ Finset.Icc 1 (R ^ 2 - 1),
          (((μ n : ℤ) : ℂ)) * ((Real.log (n : ℝ) : ℝ) : ℂ)) - 1 := by
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have h4 : 4 ≤ R ^ 2 := by nlinarith
  unfold pntFirstLambdaError pntFirstLambdaDual
  set X := R ^ 2 - 1 with hXdef
  have hX : 1 ≤ X := by omega
  have hle : R - 1 ≤ X := by omega
  rw [← pntFirst_lambdaError_hyperbola_total X hX]
  have hdisj : Disjoint (Finset.Ioc (R - 1) X) (Finset.Icc 1 (R - 1)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    rw [Finset.mem_Ioc] at hd1
    rw [Finset.mem_Icc] at hd2
    omega
  rw [← Finset.sum_union hdisj]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-! ## 2. Historical representation of the Λ-model transport -/

/-- Integer (Λ-normalized) density model of the PNT-first transport,
`L^Λ_R = Σ_{c<R} μ(c) (⌊X/c⌋ - (R-1))`, `X = R^2 - 1`. -/
def pntFirstLambdaModel (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (R - 1),
    (((μ c : ℤ) : ℂ)) * ((((R ^ 2 - 1) / c : ℕ) : ℂ) - ((R - 1 : ℕ) : ℂ))

/-- Discrete Mertens tail integral
`J(N) = Σ_{n=1}^{N-1} M(n)/(n(n+1)) = ∫_1^N M(t) t^{-2} dt`. -/
def pntFirstMertensTailIntegral (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N - 1), mertensSummatory n / ((n : ℂ) * ((n : ℂ) + 1))

/-- Lattice (fractional-part) sum `Φ_R = Σ_{c<R} μ(c) {X/c}`. -/
def pntFirstLatticeSum (R : ℕ) : ℂ :=
  ∑ c ∈ Finset.Icc 1 (R - 1),
    (((μ c : ℤ) : ℂ)) * ((((R ^ 2 - 1) % c : ℕ) : ℂ) / (c : ℂ))

/-- Discrete Abel summation:
`Σ_{c ≤ N} μ(c)/c = M(N)/N + J(N)` for `N ≥ 1`. -/
theorem pntFirst_sum_moebius_div_eq (N : ℕ) (hN : 1 ≤ N) :
    (∑ c ∈ Finset.Icc 1 N, (((μ c : ℤ) : ℂ)) / (c : ℂ)) =
      mertensSummatory N / (N : ℂ) + pntFirstMertensTailIntegral N := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hM1 : mertensSummatory 1 = 1 := by
        simp
      have hJ1 : pntFirstMertensTailIntegral 1 = 0 := by
        unfold pntFirstMertensTailIntegral
        rw [show (1 : ℕ) - 1 = 0 from rfl,
          Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 by norm_num), Finset.sum_empty]
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.Icc_self, Finset.sum_singleton, hM1, hJ1]
      simp
    · have ih' := ih hpos
      have hJ : pntFirstMertensTailIntegral (n + 1) =
          pntFirstMertensTailIntegral n +
            mertensSummatory n / ((n : ℂ) * ((n : ℂ) + 1)) := by
        unfold pntFirstMertensTailIntegral
        rw [show n + 1 - 1 = n - 1 + 1 by omega,
          Finset.sum_Icc_succ_top (by omega : 1 ≤ n - 1 + 1),
          show n - 1 + 1 = n by omega]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih', hJ,
        mertensSummatory_succ]
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp
      ring

/-- **Historical representation of the Λ-model transport.**  For `R ≥ 2` and
`X = R^2 - 1`: `L^Λ_R = X·J(R-1) + 2 M(R-1) - Φ_R`. -/
theorem pntFirstLambdaModel_eq (R : ℕ) (hR : 2 ≤ R) :
    pntFirstLambdaModel R =
      ((R ^ 2 - 1 : ℕ) : ℂ) * pntFirstMertensTailIntegral (R - 1) +
        2 * mertensSummatory (R - 1) - pntFirstLatticeSum R := by
  unfold pntFirstLambdaModel pntFirstLatticeSum
  set X := R ^ 2 - 1 with hXdef
  set N := R - 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hRN : R = N + 1 := by omega
  have hXN : X = N * (N + 2) := by
    have hsq : (N + 1) ^ 2 = N * (N + 2) + 1 := by ring
    rw [hXdef, hRN, hsq, Nat.add_sub_cancel]
  have hfloor : ∀ c ∈ Finset.Icc 1 N,
      (((μ c : ℤ) : ℂ)) * (((X / c : ℕ) : ℂ) - (N : ℂ)) =
        (X : ℂ) * ((((μ c : ℤ) : ℂ)) / (c : ℂ)) -
          (((μ c : ℤ) : ℂ)) * (((X % c : ℕ) : ℂ) / (c : ℂ)) -
            (N : ℂ) * (((μ c : ℤ) : ℂ)) := by
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdm : ((X / c : ℕ) : ℂ) = (X : ℂ) / c - ((X % c : ℕ) : ℂ) / c := by
      have h := Nat.div_add_mod X c
      have h' : (c : ℂ) * ((X / c : ℕ) : ℂ) + ((X % c : ℕ) : ℂ) = (X : ℂ) := by
        exact_mod_cast h
      field_simp
      linear_combination h'
    rw [hdm]
    ring
  rw [Finset.sum_congr rfl hfloor, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, pntFirst_sum_moebius_div_eq N hN1,
    ← mertensSummatory_eq_sum_Icc]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hXN]
  push_cast
  field_simp
  ring

/-! ## 3. #915 anchor localization of the cofactor windows -/

/-- Every cofactor `c ≥ 4` has its PNT-error window top `⌊(R^2-1)/c⌋` strictly
below the square of the #915 half-run start `A = ⌊R/2⌋ + 1`, for every `R`. -/
theorem pntFirst_cofactorWindow_below_anchor (R c : ℕ) (hc : 4 ≤ c) :
    (R ^ 2 - 1) / c < (R / 2 + 1) ^ 2 := by
  have h2 : R < 2 * (R / 2 + 1) := by omega
  have hsq : R ^ 2 < (2 * (R / 2 + 1)) ^ 2 := Nat.pow_lt_pow_left h2 (by norm_num)
  have hA : R ^ 2 - 1 < 4 * (R / 2 + 1) ^ 2 := by
    calc R ^ 2 - 1 ≤ R ^ 2 := Nat.sub_le _ _
      _ < (2 * (R / 2 + 1)) ^ 2 := hsq
      _ = 4 * (R / 2 + 1) ^ 2 := by ring
  calc (R ^ 2 - 1) / c ≤ (R ^ 2 - 1) / 4 := Nat.div_le_div_left hc (by norm_num)
    _ < (R / 2 + 1) ^ 2 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4), mul_comm]
      exact hA

/-- For `R ≥ 13` the cofactors `c = 1, 2, 3` reach the #915 half-run. -/
theorem pntFirst_cofactorWindow_inRun (R c : ℕ) (hR : 13 ≤ R) (hc1 : 1 ≤ c)
    (hc3 : c ≤ 3) :
    (R / 2 + 1) ^ 2 ≤ (R ^ 2 - 1) / c := by
  have key : 3 * (R / 2 + 1) ^ 2 ≤ R ^ 2 - 1 := by
    rcases Nat.even_or_odd R with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk2 : R / 2 = k := by omega
      have hk7 : 7 ≤ k := by omega
      have h : 3 * (k + 1) ^ 2 + 1 ≤ (k + k) ^ 2 := by nlinarith
      rw [hk2, hk]
      exact Nat.le_sub_of_add_le h
    · have hk2 : R / 2 = k := by omega
      have hk6 : 6 ≤ k := by omega
      have h : 3 * (k + 1) ^ 2 + 1 ≤ (2 * k + 1) ^ 2 := by nlinarith
      rw [hk2, hk]
      exact Nat.le_sub_of_add_le h
  calc (R / 2 + 1) ^ 2 ≤ (R ^ 2 - 1) / 3 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3), mul_comm]
        exact key
    _ ≤ (R ^ 2 - 1) / c := Nat.div_le_div_left hc3 hc1

/-- **#915 anchor localization.**  For `R ≥ 13` and `c ≥ 1`, the cofactor-`c`
window top reaches the half-run block range iff `c ≤ 3`. -/
theorem pntFirst_cofactorWindow_inRun_iff (R c : ℕ) (hR : 13 ≤ R) (hc1 : 1 ≤ c) :
    (R / 2 + 1) ^ 2 ≤ (R ^ 2 - 1) / c ↔ c ≤ 3 := by
  constructor
  · intro h
    by_contra hc
    have hlt := pntFirst_cofactorWindow_below_anchor R c (by omega)
    exact absurd (lt_of_le_of_lt h hlt) (lt_irrefl _)
  · intro hc3
    exact pntFirst_cofactorWindow_inRun R c hR hc1 hc3

/-- Block-index form: `A ≤ ⌊√⌊(R^2-1)/c⌋⌋ ↔ c ≤ 3` for `R ≥ 13`, `c ≥ 1`. -/
theorem pntFirst_cofactorWindow_height_inRun_iff (R c : ℕ) (hR : 13 ≤ R)
    (hc1 : 1 ≤ c) :
    R / 2 + 1 ≤ Nat.sqrt ((R ^ 2 - 1) / c) ↔ c ≤ 3 := by
  rw [Nat.le_sqrt, ← pow_two]
  exact pntFirst_cofactorWindow_inRun_iff R c hR hc1

end RHLean.Analysis

#print axioms RHLean.Analysis.pntFirst_moebiusLog_divisorSum_complex
#print axioms RHLean.Analysis.pntFirst_landau_vonMangoldt_mertens
#print axioms RHLean.Analysis.pntFirst_lambdaError_hyperbola_total
#print axioms RHLean.Analysis.pntFirstLambdaError_add_dual
#print axioms RHLean.Analysis.pntFirst_sum_moebius_div_eq
#print axioms RHLean.Analysis.pntFirstLambdaModel_eq
#print axioms RHLean.Analysis.pntFirst_cofactorWindow_below_anchor
#print axioms RHLean.Analysis.pntFirst_cofactorWindow_inRun
#print axioms RHLean.Analysis.pntFirst_cofactorWindow_inRun_iff
#print axioms RHLean.Analysis.pntFirst_cofactorWindow_height_inRun_iff
